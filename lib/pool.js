"use strict";
const debug = require('debug')('pool');
const uuidV4 = require('uuid/v4');
const crypto = require('crypto');
const bignum = require('bignum');
const cluster = require('cluster');
const btcValidator = require('wallet-address-validator');
const async = require('async');
const net = require('net');
const tls = require('tls');
const fs = require('fs');
const child_process = require('child_process');
const zmq = require('zeromq');
const protobuf = require("protobufjs");

const httpResponse = ' 200 OK\nContent-Type: text/plain\nContent-Length: 18\n\nMining Pool Online';
const nonceCheck32 = new RegExp("^[0-9a-f]{8}$");
const nonceCheck64 = new RegExp("^[0-9a-f]{16}$");
const hexMatch     = new RegExp("^[0-9a-f]+$");
const baseDiff     = global.coinFuncs.baseDiff();

let bannedIPs = {};
let bannedAddresses = {};
let notifyAddresses = {};

let activeMiners = new Map();

let lastBlockHash        = {}; // coin key
let lastCoinHashFactor   = {}; // coin key, last set individual coin hash factor
let currCoinHashFactor   = {}; // coin key, current individual coin hash factor
let currCoinHashFactorMM = {}; // coin key, current individual coin hash factor that includes merged mining factor
let activeBlockTemplates = {}; // coin key
let pastBlockTemplates   = {}; // coin key -> global.support.circularBuffer -> activeBlockTemplates

let lastPortErrorTime = {}; // main coin port

let lastBlockFixTime  = {}; // time when blocks were checked to be in line with other nodes or when fix_daemon_sh was attempted
let lastBlockFixCount = {}; // number of times fix_daemon_sh was run

let threadName;
let minerCount = [];
let BlockTemplate = global.coinFuncs.BlockTemplate;
let totalShares = 0, trustedShares = 0, normalShares = 0, invalidShares = 0, outdatedShares = 0, throttledShares = 0;

// wallet -> { connectTime, count (miner), hashes, last_ver_shares }
// this is need to thottle down some high share count miners
let minerWallets = {};
const MAX_VER_SHARES_PER_SEC = 10; // per thread
const VER_SHARES_PERIOD = 5;

Buffer.prototype.toByteArray = function () {
    return Array.prototype.slice.call(this, 0);
};

// Define proto message
const ShareMessage = !!!config.publisherJson ?
    new protobuf.Type("ShareMessage")
    .add(new protobuf.Field("poolId", 1, "string"))
    .add(new protobuf.Field("miner", 2, "string"))
    .add(new protobuf.Field("worker", 3, "string"))
    .add(new protobuf.Field("payoutInfo", 4, "string"))
    .add(new protobuf.Field("userAgent", 5, "string"))
    .add(new protobuf.Field("ipAddress", 6, "string"))
    .add(new protobuf.Field("source", 7, "string"))
    .add(new protobuf.Field("difficulty", 8, "double"))
    .add(new protobuf.Field("blockHeight", 9, "int64"))
    .add(new protobuf.Field("blockReward", 10, "double"))
    .add(new protobuf.Field("blockHash", 11, "string"))
    .add(new protobuf.Field("isBlockCandidate", 12, "bool"))
    .add(new protobuf.Field("transactionConfirmationData", 13, "string"))
    .add(new protobuf.Field("networkDifficulty", 14, "double")) : undefined;

// connect/bind ZMQ share publisher socket
const pubSock = zmq.socket('pub');
const pubFlags = config.publisherJson ? 1 : 2;  // WireFormat.Json or WireFormat.ProtoBuf
const pubFlagsBuf = Buffer.allocUnsafe(4);
pubFlagsBuf.writeUInt32BE(pubFlags, 0);

if(!config.publisherConnect) {
    pubSock.bindSync(config.publisherSocket);
    console.log('Bound to publisher ZMQ socket ' + config.publisherSocket);
} else {
    pubSock.connect(config.publisherSocket);
    console.log('Connected to publisher ZMQ socket ' + config.publisherSocket);
}

if (cluster.isMaster) {
    threadName = "(Master) ";
    setInterval(function () {
        let trustedSharesPercent   = (totalShares ? trustedShares   / totalShares * 100 : 0).toFixed(2);
        let normalSharesPercent    = (totalShares ? normalShares    / totalShares * 100 : 0).toFixed(2);
        let invalidSharesPercent   = (totalShares ? invalidShares   / totalShares * 100 : 0).toFixed(2);
        let outdatedSharesPercent  = (totalShares ? outdatedShares  / totalShares * 100 : 0).toFixed(2);
        let throttledSharesPercent = (totalShares ? throttledShares / totalShares * 100 : 0).toFixed(2);
        console.log(`>>> Trusted=${trustedShares}(${trustedSharesPercent}%) / Validated=${normalShares}(${normalSharesPercent}%) / Invalid=${invalidShares}(${invalidSharesPercent}%) / Outdated=${outdatedShares}(${outdatedSharesPercent}%) / Throttled=${throttledShares}(${throttledSharesPercent}%) / Total=${totalShares} shares`);
        totalShares     = 0;
        trustedShares   = 0;
        normalShares    = 0;
        invalidShares   = 0;
        outdatedShares  = 0;
        throttledShares = 0;
    }, 30*1000);
} else {
    threadName = "(Worker " + cluster.worker.id + " - " + process.pid + ") ";
    // reset last verified share counters every VER_SHARES_PERIOD seconds
    setInterval(function () {
       for (let wallet in minerWallets) {
           minerWallets[wallet].last_ver_shares = 0;
       }
    }, VER_SHARES_PERIOD*1000);
}

const COINS = global.coinFuncs.getCOINS();

// Master/Slave communication Handling
function messageHandler(message) {
    switch (message.type) {
        case 'banIP':
            debug(threadName + "Received ban IP update from nodes");
            if (cluster.isMaster) {
                sendToWorkers(message);
            } else {
                bannedIPs[message.data] = 1;
            }
            break;
        case 'newBlockTemplate':
            debug(threadName + "Received new block template");
            setNewBlockTemplate(message.data);
            break;
        case 'newCoinHashFactor':
            debug(threadName + "Received new coin hash factor");
            setNewCoinHashFactor(true, message.data.coin, message.data.coinHashFactor);
            break;
        case 'minerPortCount':
            if (cluster.isMaster) minerCount[message.data.worker_id] = message.data.ports;
            break;
        case 'sendRemote':
            if (cluster.isMaster) {
                global.database.sendQueue.push({body: Buffer.from(message.body, 'hex')});
            }
            break;
        case 'trustedShare':
            ++ trustedShares;
            ++ totalShares;
            break;
        case 'normalShare':
            ++ normalShares;
            ++ totalShares;
            break;
        case 'invalidShare':
            ++ invalidShares;
            ++ totalShares;
            break;
        case 'outdatedShare':
            ++ outdatedShares;
            // total shares will be also increased separately as part of share type above
            break;
        case 'throttledShare':
            ++ throttledShares;
            ++ totalShares;
            break;
    }
}

process.on('message', messageHandler);

function sendToWorkers(data) {
    Object.keys(cluster.workers).forEach(function(key) {
        cluster.workers[key].send(data);
    });
}

function adjustMinerDiff(miner) {
    if (miner.fixed_diff) {
        const newDiff = miner.calcNewDiff();
        if (miner.difficulty * 10 < newDiff) {
            console.log("Dropped low fixed diff " + miner.difficulty + " for " + miner.logString + " miner to " + newDiff + " dynamic diff");
            miner.fixed_diff = false;
            if (miner.setNewDiff(newDiff)) return true;
        }
    } else if (miner.setNewDiff(miner.calcNewDiff())) {
        return true;
    }
    return false;
}

function retargetMiners() {
    debug(threadName + "Performing difficulty check on miners");

    global.config.ports.forEach(function (portData) { minerCount[portData.port] = 0; });
    const time_before = Date.now();
    for (var [minerId, miner] of activeMiners) {
        if (adjustMinerDiff(miner)) miner.sendSameCoinJob();
        ++ minerCount[miner.port];
    }
    const elapsed = Date.now() - time_before;
    if (elapsed > 50) console.error(threadName + "retargetMiners() consumed " + elapsed + " ms for " + activeMiners.size + " miners");
    process.send({type: 'minerPortCount', data: { worker_id: cluster.worker.id, ports: minerCount } });
}

function removeMiner(miner) {
    const proxyMinerName = miner.proxyMinerName;
    if (proxyMinerName && proxyMinerName in proxyMiners && --proxyMiners[proxyMinerName].count <= 0) delete proxyMiners[proxyMinerName];
    if (miner.payout in minerWallets && --minerWallets[miner.payout].count <= 0) delete minerWallets[miner.payout]; 
    activeMiners.delete(miner.id);
}

function checkAliveMiners() {
    debug(threadName + "Verifying if miners are still alive");
    const time_before = Date.now();
    const deadline = time_before - global.config.pool.minerTimeout * 1000;
    for (var [minerId, miner] of activeMiners) if (miner.lastContact < deadline) removeMiner(miner);
    const elapsed = Date.now() - time_before;
    if (elapsed > 50) console.error(threadName + "checkAliveMiners() consumed " + elapsed + " ms for " + activeMiners.size + " miners");
}

function set_hash_factor(coin, hash_factor) {
    currCoinHashFactor[coin] = hash_factor;
}

// global.config.daemon["activePort" + coin] is only updated in master thread
function updateActivePort(coin) {
    global.support.getActivePort(coin, function (newActivePort) {
        const oldActivePort = global.config.daemon["activePort" + coin];
        if (newActivePort === null) {
            if (coin === "" && oldActivePort != global.config.daemon.port) {
                console.error("Error getting activePort, so rolling back to main port");
                global.config.daemon.activePort = global.config.daemon.port;
            } else {
                console.error("Error getting activePort" + coin);
                coinHashFactorUpdate(coin, 0);
            }
        } else {
            if (coin !== "") {
                global.support.getCoinHashFactor(coin, function (newCoinHashFactor) {
                    if (newCoinHashFactor === null) {
                        console.error("Error getting coinHashFactor" + coin);
                        coinHashFactorUpdate(coin, 0);
                    } else {
                        if (!newActivePort || !newCoinHashFactor) coinHashFactorUpdate(coin, 0);
                        else set_hash_factor(coin, newCoinHashFactor);
                        if (oldActivePort !== newActivePort) {
                            console.log("Changing activePort" + coin + " from " + oldActivePort + " to " + newActivePort);
                            global.config.daemon["activePort" + coin] = newActivePort;
                        }
                    }
                });
            } else if (oldActivePort !== newActivePort) {
                if (!(newActivePort in lastPortErrorTime) || Date.now() - lastPortErrorTime[newActivePort] > 30*60*1000) {
                    console.log("Changing activePort" + coin + " from " + oldActivePort + " to " + newActivePort);
                    global.config.daemon["activePort" + coin] = newActivePort;
                } else if ((Date.now() - lastPortErrorTime[newActivePort]) % 60*1000 < 6*1000) { // print every 10th message
                    console.warn("Avoiding changing recently problem activePort" + coin + " from " + oldActivePort + " to " + newActivePort);
                }
            }
        }
    });
}

function process_rpc_template(rpc_template, coin, port, coinHashFactor, isHashFactorChange) {
    let template = Object.assign({}, rpc_template);

    template.coin               = coin;
    template.port               = parseInt(port);
    template.coinHashFactor     = coinHashFactor;
    template.isHashFactorChange = isHashFactorChange;

    if (port in global.coinFuncs.getMM_PORTS()) {
        const child_coin = global.coinFuncs.PORT2COIN(global.coinFuncs.getMM_PORTS()[port]);
        if (child_coin in activeBlockTemplates) {
            template.child_template            = activeBlockTemplates[child_coin];
            template.child_template_buffer     = template.child_template.buffer;
            template.parent_blocktemplate_blob = global.coinFuncs.constructMMParentBlockBlob(
                new Buffer(rpc_template.blocktemplate_blob, 'hex'), port, template.child_template_buffer
            ).toString('hex');
        }
    }

    return template;
}

// templateUpdateReal is only called in master thread (except the beginning of a worker thread)
function templateUpdateReal(coin, activePort, coinHashFactor, isHashFactorChange) {
    global.coinFuncs.getPortBlockTemplate(activePort, function (rpcResponse) {
        if (activePort !== global.config.daemon["activePort" + coin]) {
            console.log("Aborting " + activePort + " last block template request because " + "activePort" + coin + " was already changed to " + global.config.daemon["activePort" + coin] + " port");
            return;
        }
        if (rpcResponse && typeof rpcResponse.result !== 'undefined') {
            const rpc_template = rpcResponse.result;
            const template = process_rpc_template(rpc_template, coin, activePort, coinHashFactor, isHashFactorChange);
            debug(threadName + "New block template found at " + rpc_template.height + " height");
            if (cluster.isMaster) {
                sendToWorkers({type: 'newBlockTemplate', data: template});
                setNewBlockTemplate(template);
                // update parent coins if current coin was updated now
                if (activePort in global.coinFuncs.getMM_CHILD_PORTS()) {
                    const parent_ports = global.coinFuncs.getMM_CHILD_PORTS()[activePort];
                    for (let parent_port in parent_ports) {
                        const parent_coin = global.coinFuncs.PORT2COIN(parent_port);
                        if (parent_coin in activeBlockTemplates) {
                            const parent_template = process_rpc_template(activeBlockTemplates[parent_coin], parent_coin, parent_port, currCoinHashFactor[parent_coin], false);
                            sendToWorkers({type: 'newBlockTemplate', data: parent_template});
                            setNewBlockTemplate(parent_template);
                        }
                    }
                }
            } else {
                setNewBlockTemplate(template);
            }
        } else {
            console.error("Block template request failed for " + activePort + " port.");
            coinHashFactorUpdate(coin, 0);
            setTimeout(templateUpdateReal, 3000, coin, activePort, coinHashFactor, isHashFactorChange);
        }
    });
}

function coinHashFactorUpdate(coin, coinHashFactor) {
    if (coin === "") return;
    if (currCoinHashFactor[coin] === 0 && coinHashFactor === 0) return;
    if (cluster.isMaster) {
        //console.log('[*] New ' + coin + ' coin hash factor is set from ' + currCoinHashFactor[coin] + ' to ' + coinHashFactor);
        let data = { coin: coin, coinHashFactor: coinHashFactor };
        sendToWorkers({type: 'newCoinHashFactor', data: data});
    }
    setNewCoinHashFactor(true, coin, coinHashFactor);
}

let failedPortLastBlockHeaderCoinHashFactor = {};

// templateUpdate is only called in master thread (except the beginning of a worker thread)
function templateUpdate(coin, repeating) {
    const activePort     = global.config.daemon["activePort" + coin];
    let   coinHashFactor = currCoinHashFactor[coin];
    if (activePort && (coinHashFactor || (coin in failedPortLastBlockHeaderCoinHashFactor))) global.coinFuncs.getPortLastBlockHeader(activePort, function (err, body) {
        if (coin in failedPortLastBlockHeaderCoinHashFactor) {
            if (!coinHashFactor) coinHashFactor = failedPortLastBlockHeaderCoinHashFactor[coin];
            delete failedPortLastBlockHeaderCoinHashFactor[coin];
        }
        if (activePort !== global.config.daemon["activePort" + coin]) {
            console.log(threadName + "Aborting " + activePort + " last block header request because activePort" + coin + " was already changed to " + global.config.daemon["activePort" + coin] + " port");
            if (repeating === true) setTimeout(templateUpdate, 50, coin, repeating);
        } else if (err === null) {
            const isHashFactorChange = !(coin in lastCoinHashFactor) || Math.abs(lastCoinHashFactor[coin] - coinHashFactor) / coinHashFactor > 0.05;
            if (!(coin in lastBlockHash) || body.hash !== lastBlockHash[coin]) {
                lastBlockHash[coin] = body.hash;
                templateUpdateReal(coin, activePort, coinHashFactor, isHashFactorChange);
            } else if (isHashFactorChange) {
                coinHashFactorUpdate(coin, coinHashFactor);
            }
            if (repeating === true) setTimeout(templateUpdate, 50, coin, repeating);
        } else {
            failedPortLastBlockHeaderCoinHashFactor[coin] = coinHashFactor;
            console.error(threadName + "Last block header request for " + activePort + " port failed!");
            coinHashFactorUpdate(coin, 0);
            setTimeout(templateUpdate, 1000, coin, repeating);
        }
    }); else if (cluster.isMaster) {
        //console.error(threadName + "Last block header request for " + activePort + " port was skipped!");
        coinHashFactorUpdate(coin, 0);
        setTimeout(templateUpdate, 1000, coin, repeating);
    }
}

// main chain anchor block height for alt chain block
let anchorBlockHeight;
let anchorBlockPrevHeight;

// update main chain anchor block height for alt chain block
// anchorBlockUpdate is only called in worker threads
function anchorBlockUpdate() {
    if (("" in activeBlockTemplates) && global.config.daemon.port == activeBlockTemplates[""].port) return;
    // only need to do that separately if we mine alt chain
    global.coinFuncs.getLastBlockHeader(function (err, body) {
        if (err === null) {
            anchorBlockHeight = body.height + 1;
            if (!anchorBlockPrevHeight || anchorBlockPrevHeight != anchorBlockHeight) {
                anchorBlockPrevHeight = anchorBlockHeight;
                debug("Anchor block was changed to " + anchorBlockHeight);
            }
        } else {
            console.error("Archor last block header request failed!");
        }
    });
}

function getCoinJobParams(coin) {
    let params = {};
    params.bt             = activeBlockTemplates[coin];
    params.coinHashFactor = currCoinHashFactorMM[coin];
    params.algo_name      = global.coinFuncs.algoShortTypeStr(params.bt.port, params.bt.buffer[0]);
    //params.variant_name   = params.algo_name.split('/')[1];
    return params;
};

function setNewCoinHashFactor(isHashFactorChange, coin, coinHashFactor, check_height) {
    if (isHashFactorChange) lastCoinHashFactor[coin] = coinHashFactor;

    // used in miner.selectBestCoin
    currCoinHashFactorMM[coin] = coinHashFactor;
    const port = global.coinFuncs.COIN2PORT(coin);
    const is_mm = port in global.coinFuncs.getMM_PORTS();
    if (is_mm) {
        const child_coin = global.coinFuncs.PORT2COIN(global.coinFuncs.getMM_PORTS()[port]);
        if (child_coin in lastCoinHashFactor) currCoinHashFactorMM[coin] += lastCoinHashFactor[child_coin];
    }

    if (coin !== "") {
        if (cluster.isMaster) console.log('[*] New ' + coin + ' coin hash factor is set from ' + currCoinHashFactor[coin] + ' to ' + coinHashFactor + (is_mm ? ' (MM: ' + currCoinHashFactorMM[coin] + ')' : ""));
        set_hash_factor(coin, coinHashFactor);
    }
    if (!(coin in activeBlockTemplates)) return;

    // update parent coins if current coin was updated now
    if (isHashFactorChange) if (port in global.coinFuncs.getMM_CHILD_PORTS()) {
        const parent_ports = global.coinFuncs.getMM_CHILD_PORTS()[port];
        for (let parent_port in parent_ports) {
            const parent_coin = global.coinFuncs.PORT2COIN(parent_port);
            if (parent_coin in lastCoinHashFactor) {
                setNewCoinHashFactor(true, parent_coin, lastCoinHashFactor[parent_coin], 0);
            }
        }
    }

    const time_before = Date.now();
    let strLogPrefix;

    if (isHashFactorChange) {
        const port          = activeBlockTemplates[coin].port;
        const block_version = activeBlockTemplates[coin].buffer[0];
        const algo          = global.coinFuncs.algoShortTypeStr(port, block_version);

        strLogPrefix = "Full BT update for coin " + coin;
        if (cluster.isMaster) console.log(threadName + strLogPrefix + " with hash factor changed to " + currCoinHashFactorMM[coin]);

        if (check_height) {
            for (var [minerId, miner] of activeMiners) {
                if (!global.coinFuncs.isMinerSupportAlgo(algo, miner.algos)) continue;
                miner.trust.check_height = check_height;
                miner.sendBestCoinJob();
            }
        } else {
            for (var [minerId, miner] of activeMiners) {
                if (!global.coinFuncs.isMinerSupportAlgo(algo, miner.algos)) continue;
                miner.sendBestCoinJob();
            }
        }

    } else {

        strLogPrefix = "Fast BT update for coin " + coin;
        if (cluster.isMaster) console.log(threadName + strLogPrefix + " with the same " + currCoinHashFactorMM[coin] + " hash factor");

        const params = getCoinJobParams(coin);
        if (check_height) {
            for (var [minerId, miner] of activeMiners) {
                //if (typeof(miner.curr_coin) === 'undefined') console.error("[INTERNAL ERROR]: " + miner.logString + ": undefined curr_coin");
                if (miner.curr_coin !== coin) continue;
                //if (!(coin in miner.coin_perf)) console.error("[INTERNAL ERROR]: " + miner.logString + ": no longer supported coin " + coin + " in miner " + JSON.stringify(miner.coin_perf) + " coin_perf");
                //if (!global.coinFuncs.isMinerSupportAlgo(algo, miner.algos)) console.error("[INTERNAL ERROR]: " + miner.logString + ": no longer supported algo " + algo + " in miner " + JSON.stringify(miner.algos) + " algos");
                miner.trust.check_height = check_height;
                miner.sendCoinJob(coin, params);
            }
        } else {
            for (var [minerId, miner] of activeMiners) {
                //if (typeof(miner.curr_coin) === 'undefined') console.error("[INTERNAL ERROR]: " + miner.logString + ": undefined curr_coin");
                if (miner.curr_coin !== coin) continue;
                //if (!(coin in miner.coin_perf)) console.error("[INTERNAL ERROR]: " + miner.logString + ": no longer supported coin " + coin + " in miner " + JSON.stringify(miner.coin_perf) + " coin_perf");
                //if (!global.coinFuncs.isMinerSupportAlgo(algo, miner.algos)) console.error("[INTERNAL ERROR]: " + miner.logString + ": no longer supported algo " + algo + " in miner " + JSON.stringify(miner.algos) + " algos");
                miner.sendCoinJob(coin, params);
            }
        }
    }

    const elapsed = Date.now() - time_before;
    if (elapsed > 50) console.error(threadName + strLogPrefix + " setNewCoinHashFactor() consumed " + elapsed + " ms for " + activeMiners.size + " miners");
}

function setNewBlockTemplate(template) {
    const coin = template.coin;
    let isExtraCheck = false;
    if (coin in activeBlockTemplates) {
        if (activeBlockTemplates[coin].prev_hash === template.prev_hash) {
            if ("child_template" in template) {
                if ("child_template" in activeBlockTemplates[coin] && activeBlockTemplates[coin].child_template.prev_hash === template.child_template.prev_hash) {
                    console.log(threadName + 'Ignoring duplicate parent block template update at height: ' + template.height + '. Difficulty: ' + template.difficulty);
                    return;
                }
            } else {
                console.log(threadName + 'Ignoring duplicate block template update at height: ' + template.height + '. Difficulty: ' + template.difficulty);
                return;
            }
        }
        activeBlockTemplates[coin].timeOutdate = Date.now() + 4*1000;
        if (!(coin in pastBlockTemplates)) pastBlockTemplates[coin] = global.support.circularBuffer(10);
        pastBlockTemplates[coin].enq(activeBlockTemplates[coin]);
        if (activeBlockTemplates[coin].port != template.port && global.config.pool.trustedMiners) isExtraCheck = true;
    }
    if (cluster.isMaster) {
        const coin_str = coin === "" ? "" : coin + " ";
        console.log('[*] New ' + coin_str + 'block to mine at ' + template.height + ' height with ' + template.difficulty + ' difficulty and ' + template.port + ' port (with coin hash factor ' + template.coinHashFactor + ")");
    } else {
        debug(threadName + 'New block to mine at ' + template.height + ' height with ' + template.difficulty + ' difficulty and ' + template.port + ' port');
    }

    activeBlockTemplates[coin] = new BlockTemplate(template);

    const height = activeBlockTemplates[coin].height;

    if (coin === "" && global.config.daemon.port == activeBlockTemplates[""].port) {
        anchorBlockHeight = height;
    }

    setNewCoinHashFactor(template.isHashFactorChange, coin, template.coinHashFactor, isExtraCheck ? height : 0);
}

// here we keep verified share number of a specific wallet (miner.payout)
// it will reset to 0 after invalid share is found
// if walletTrust exceeds certain threshold (global.config.pool.trustThreshold * 100) then low diff (<=16000) new workers for this wallet are started with high trust
// this is needed to avoid CPU overload after constant miner reconnections that happen during mining botnet swarms
let walletTrust = {};
// wallet last seen time (all wallets that are not detected for more than 1 day are removed)
let walletLastSeeTime = {};

// miner agent strings (for cluster.worker.id == 1)
let minerAgents = {};

var reEmail = /^\S+@\S+\.\S+$/;
// wallet password last check time
let walletLastCheckTime = {};

//let cacheTargetHex = {};

function getTargetHex(difficulty, size) {
    //const result = cacheTargetHex[difficulty];
    //if (result) return result;
    let padded = new Buffer(32);
    padded.fill(0);
    const diffBuff = baseDiff.div(difficulty).toBuffer();
    diffBuff.copy(padded, 32 - diffBuff.length);
    const buff = padded.slice(0, size);
    const buffArray = buff.toByteArray().reverse();
    const buffReversed = new Buffer(buffArray);
    const new_result = buffReversed.toString('hex');
    //cacheTargetHex[difficulty] = new_result;
    return new_result;
};

function Miner(id, login, pass, ipAddress, startingDiff, messageSender, protoVersion, portType, port, agent, algos, algos_perf, algo_min_time) {
    // Username Layout - <address in BTC or XMR>.<Difficulty>
    // Password Layout - <password>.<miner identifier>.<payment ID for XMR>
    // Default function is to use the password so they can login.  Identifiers can be unique, payment ID is last.
    // If there is no miner identifier, then the miner identifier is set to the password
    // If the password is x, aka, old-logins, we're not going to allow detailed review of miners.

    const login_diff_split      = login.split("+");
    const login_div_split       = login_diff_split[0].split("%");
    const login_paymentid_split = login_div_split[0].split(".");
    const pass_algo_split       = pass.split("~");
    let   pass_split            = pass_algo_split[0].split(":");

    // Workaround for a common mistake to put email without : before it
    // and also security measure to hide emails used as worker names
    if (pass_split.length === 1 && reEmail.test(pass_split[0])) {
        pass_split.push(pass_split[0]);
        pass_split[0] = "email";
    }

    // 1) set payout, identifier, email and logString

    this.payout = this.address = login_paymentid_split[0];
    this.paymentID = null;

    this.identifier = agent && agent.includes('MinerGate') ? "MinerGate" : pass_split[0].substring(0, 64);
    if (typeof(login_paymentid_split[1]) !== 'undefined') {
        if (login_paymentid_split[1].length === 64 && hexMatch.test(login_paymentid_split[1]) && global.coinFuncs.validatePlainAddress(this.address)) {
            this.paymentID = login_paymentid_split[1];
            this.payout += "." + this.paymentID;
            if (typeof(login_paymentid_split[2]) !== 'undefined' && this.identifier === 'x') {
                this.identifier = login_paymentid_split[2].substring(0, 64);
            }
        } else if (this.identifier === 'x') {
            this.identifier = login_paymentid_split[1].substring(0, 64);
        }
    }

    this.debugMiner = this.payout == global.coinFuncs.testDevAddress;
    this.email      = pass_split.length === 2 ? pass_split[1] : "";
    this.logString  = this.payout.substr(this.payout.length - 10) + ":" + this.identifier + " (" + ipAddress + ")";

    // 2) check stuff

    if (login_diff_split.length > 2) {
        this.error = "Please use monero_address[.payment_id][+difficulty_number] login/user format";
        this.valid_miner = false;
        return;
    }

    if (Math.abs(login_div_split.length % 2) == 0 || login_div_split.length > 5) {
        this.error = "Please use monero_address[.payment_id][%N%95_char_long_monero_wallet_address]+[+difficulty_number] login/user format";
        this.valid_miner = false;
        return;
    }

    this.payout_div = {};

    let payout_percent_left = 100;
    for (let index = 1; index < login_div_split.length - 1; index += 2) {
        const percent = parseFloat(login_div_split[index]);
        if (isNaN(percent) || percent < 0.1) {
            this.error = "Your payment divide split " + percent + " is below 0.1% and can't be processed";
            this.valid_miner = false;
            return;
        }
        if (percent > 99.9) {
            this.error = "Your payment divide split " + percent + " is above 99.9% and can't be processed";
            this.valid_miner = false;
            return;
        }
        payout_percent_left -= percent;
        if (payout_percent_left < 0.1) {
            this.error = "Your summary payment divide split exceeds 99.9% and can't be processed";
            this.valid_miner = false;
            return;
        }
        const address = login_div_split[index + 1];
        if (address.length != 95 || !global.coinFuncs.validateAddress(address)) {
            this.error = "Invalid payment address provided: " + address + ". Please use 95_char_long_monero_wallet_address format";
            this.valid_miner = false;
            return;
        }
        if (address in bannedAddresses) { // Banned Address
            this.error = "Permanently banned payment address " + address + " provided: " + bannedAddresses[address];
            this.valid_miner = false;
            return;
        }
        if (address in this.payout_div) {
            this.error = "You can't repeat payment split address " + address;
            this.valid_miner = false;
            return;
        }
        this.payout_div[address] = percent;
    }

    if (payout_percent_left === 100) {
        this.payout_div = null;
    } else {
        if (this.payout in this.payout_div) {
            this.error = "You can't repeat payment split address " + this.payout;
            this.valid_miner = false;
            return;
        }
        this.payout_div[this.payout] = payout_percent_left;
    }

    if (pass_split.length > 2) {
        this.error = "Please use worker_name[:email] password format";
        this.valid_miner = false;
        return;
    }

    if (this.payout in bannedAddresses) { // Banned Address
        this.error = "Permanently banned payment address " + this.payout + " provided: " + bannedAddresses[this.payout];
        this.valid_miner = false;
        return;
    }

    if (global.coinFuncs.exchangeAddresses.indexOf(this.address) !== -1 && !(this.paymentID)) {
        this.error = "Exchange addresses need 64 hex character long payment IDs. Please specify it after your wallet address as follows after dot: Wallet.PaymentID";
        this.valid_miner = false;
        return;
    }

    if (global.coinFuncs.validateAddress(this.address)) {
        this.bitcoin = 0;
    } else if (global.config.general.allowBitcoin && global.coinFuncs.supportsAutoExchange && btcValidator.validate(this.address)) {
        this.bitcoin = 1;
    } else {
        this.error = "Invalid payment address provided: " + this.address + ". Please use 95_char_long_monero_wallet_address format";
        this.valid_miner = false;
        return;
    }

    if (!("" in activeBlockTemplates)) {
        this.error = "No active block template";
        this.valid_miner = false;
        return;
    }

    this.setAlgos = function(algos, algos_perf, algo_min_time) {
        this.algos = {};
        for (let i in algos) this.algos[algos[i]] = 1;
        const check = global.coinFuncs.algoCheck(this.algos);
        if (check !== true) return check;
        if ("cn-pico" in this.algos) this.algos["cn-pico/trtl"] = 1;
        let coin_perf = global.coinFuncs.convertAlgosToCoinPerf(algos_perf);
        if (coin_perf instanceof Object) {
            if (!("" in coin_perf) || !global.coinFuncs.algoMainCheck(this.algos)) coin_perf[""] = 1.0e-12;
            this.coin_perf = coin_perf;
        } else {
            return coin_perf;
        }
        this.algo_min_time = algo_min_time ? algo_min_time : 0;
        return "";
    };

    if (pass_algo_split.length == 2) {
       const algo_name = pass_algo_split[1];
       algos         = [ algo_name ];
       algos_perf    = {};
       algos_perf[algo_name] = 1;
       algo_min_time = 0;

    } else {
        if (algos && algos instanceof Array && global.config.daemon.enableAlgoSwitching) {
           if (!algos_perf || !(algos_perf instanceof Object)) algos_perf = global.coinFuncs.getDefaultAlgosPerf();
        } else {
           algos         = global.coinFuncs.getDefaultAlgos();
           algos_perf    = global.coinFuncs.getDefaultAlgosPerf();
           algo_min_time = 0;
        }
    }
    const status = this.setAlgos(algos, algos_perf, algo_min_time);
    if (status != "") {
        this.error = status;
        this.valid_miner = false;
        return;
    }


    // 3) setup valid miner stuff

    // 3a) misc stuff

    this.error = "";
    this.valid_miner = true;

    this.proxy = agent && agent.includes('xmr-node-proxy');
    this.id = id;
    this.ipAddress = ipAddress;
    this.messageSender = messageSender;
    this.connectTime = Date.now();
    this.heartbeat = function () { this.lastContact = Date.now(); };
    this.heartbeat();

    // 3b) port stuff
   
    this.port = port;
    this.portType = portType;
    switch (portType) {
        case 'pplns': this.poolTypeEnum = global.protos.POOLTYPE.PPLNS; break;
        case 'pps':   this.poolTypeEnum = global.protos.POOLTYPE.PPS;   break;
        case 'solo':  this.poolTypeEnum = global.protos.POOLTYPE.SOLO;  break;
        case 'prop':  this.poolTypeEnum = global.protos.POOLTYPE.PROP;  break;
        default:      console.error("Wrong portType " + portType);
                      this.poolTypeEnum = global.protos.POOLTYPE.PPLNS;
    }

    this.wallet_key = this.payout + " " + this.bitcoin + " " + this.poolTypeEnum + " " + JSON.stringify(this.payout_div) + " ";

    // 3c) diff stuff

    this.lastShareTime = Math.floor(Date.now() / 1000);
    this.validShares = 0;
    this.invalidShares = 0;
    this.hashes = 0;

    this.fixed_diff = false;
    this.difficulty = startingDiff;

    if (agent && agent.includes('NiceHash')) {
        this.fixed_diff = true;
        this.difficulty = global.coinFuncs.niceHashDiff;
    }
    if (login_diff_split.length === 2) {
        this.fixed_diff = true;
        this.difficulty = Number(login_diff_split[1]);
        if (this.difficulty < global.config.pool.minDifficulty) {
            this.difficulty = global.config.pool.minDifficulty;
        }
        if (this.difficulty > global.config.pool.maxDifficulty) {
            this.difficulty = global.config.pool.maxDifficulty;
        }
    }

    // 3d) trust stuff

    if (global.config.pool.trustedMiners) {
        if (!(this.payout in walletTrust)) {
            walletTrust[this.payout] = 0;
            walletLastSeeTime[this.payout] = Date.now();
        }
        this.trust = {
            trust:        0,
            check_height: 0
        };
    }

    // 3e) password setup stuff

    let email = this.email.trim();
    if (email != "") {
        // Need to do an initial registration call here.  Might as well do it right...
        let payoutAddress = this.payout;
        let time_now = Date.now();
        if (!(payoutAddress in walletLastCheckTime) || time_now - walletLastCheckTime[payoutAddress] > 60*1000) {
            global.mysql.query("SELECT id FROM users WHERE username = ? LIMIT 1", [payoutAddress]).then(function (rows) {
                if (rows.length > 0) return;
                if (global.coinFuncs.blockedAddresses.indexOf(payoutAddress) !== -1) return;
                global.mysql.query("INSERT INTO users (username, email) VALUES (?, ?)", [payoutAddress, email]);
                console.log("Setting password " + email + " for " + payoutAddress);
            });
            walletLastCheckTime[payoutAddress] = time_now;
        }
    }

    this.validJobs = global.support.circularBuffer(10);
    this.cachedJob = null;

    this.storeInvalidShare = function() {
        global.database.storeInvalidShare(global.protos.InvalidShare.encode({
            paymentAddress: this.address,
            paymentID:      this.paymentID,
            identifier:     this.identifier
        }));
    };

    this.selectBestCoin = function() {
        if (this.debugMiner) console.log(threadName + this.logString + ": current coin is " + this.curr_coin);
        if (typeof(this.curr_coin) !== 'undefined' && this.curr_coin_time && currCoinHashFactorMM[this.curr_coin] &&
            Date.now() - this.curr_coin_time < this.algo_min_time*1000
        ) {
           return this.curr_coin;
        }
        let best_coin = "";
        let best_coin_perf = this.coin_perf[""] * 1.1;
        let miner = this;
        COINS.forEach(function(coin) {
            if (!(coin in miner.coin_perf)) {
              if (miner.debugMiner) console.log(threadName + miner.logString + ": " + coin + ": no coin_perf");
              return;
            }
            if (!(coin in activeBlockTemplates)) {
              if (miner.debugMiner) console.log(threadName + miner.logString + ": " + coin + ": no activeBlockTemplates");
              return;
            }
            const coinHashFactor = currCoinHashFactorMM[coin];
            if (!coinHashFactor) {
              if (miner.debugMiner) console.log(threadName + miner.logString + ": " + coin + ": no coinHashFactor");
              return;
            }
            const bt            = activeBlockTemplates[coin];
            const port          = bt.port;
            const block_version = bt.buffer[0];
            const algo          = global.coinFuncs.algoShortTypeStr(port, block_version);
            if (!global.coinFuncs.isMinerSupportAlgo(algo, miner.algos)) {
              if (miner.debugMiner) console.log(threadName + miner.logString + ": " + coin + ": no algo support");
              return;
            }
            let coin_perf = miner.coin_perf[coin] * coinHashFactor;
            if (miner.curr_coin === coin) coin_perf *= 1.05;
            if (miner.debugMiner) console.log(threadName + miner.logString + ": " + coin + ": " + coin_perf);
            if (coin_perf > best_coin_perf) {
                best_coin      = coin;
                best_coin_perf = coin_perf;
            }
        });
        if (typeof(this.curr_coin) === 'undefined' || this.curr_coin != best_coin) {
            const curr_hash_factor = typeof(this.curr_coin_hash_factor) === 'undefined' ? 1 : this.curr_coin_hash_factor;
            const factor = curr_hash_factor / currCoinHashFactorMM[best_coin];
            if (factor != 1) {
                if (this.hashes === 0) {
                    this.setNewDiff(this.difficulty * factor);
                } else {
                    this.hashes *= factor;
                    if (this.hashesShift) this.hashesShift *= factor;
                    this.setNewDiff(this.calcNewDiff());
                }
            }
            this.curr_coin             = best_coin;
            this.curr_coin_hash_factor = currCoinHashFactorMM[best_coin];
            this.curr_coin_time        = Date.now();
            if (global.config.pool.trustedMiners) this.trust.check_height = activeBlockTemplates[best_coin].height;
        }
        return best_coin;
    };

    this.calcNewDiff = function () {
        const proxyMinerName = this.payout + ":" + this.identifier;
        let miner;
        let target;
        let min_diff;
        let history_time;
        if (proxyMinerName in proxyMiners) {
            miner = proxyMiners[proxyMinerName];
            target = 5;
            min_diff = 10*global.config.pool.minDifficulty;
            history_time = 5;
            if (this.debugMiner) console.log(threadName + this.logString + ": calc proxy miner diff: " + miner.hashes + " / " + ((Date.now() - miner.connectTime) / 1000));
        } else if (this.payout in minerWallets && minerWallets[this.payout].last_ver_shares >= MAX_VER_SHARES_PER_SEC * VER_SHARES_PERIOD) {
            miner = minerWallets[this.payout];
            target = 5;
            min_diff = 10*global.config.pool.minDifficulty;
            history_time = 5;
            if (this.debugMiner) console.log(threadName + this.logString + ": calc throttled miner diff: " + miner.hashes + " / " + ((Date.now() - miner.connectTime) / 1000));
        } else {
            miner = this;
            target = this.proxy ? 5 : global.config.pool.targetTime;
            min_diff = this.proxy ? 10*global.config.pool.minDifficulty : global.config.pool.minDifficulty;
            history_time = 60;
            if (this.debugMiner) console.log(threadName + this.logString + ": calc miner diff: " + miner.hashes + " / " + ((Date.now() - miner.connectTime) / 1000));
        }
        if (miner.connectTimeShift) {
            if (Date.now() - miner.connectTimeShift > history_time*60*1000) {
                miner.connectTime = miner.connectTimeShift;
                miner.hashes -= miner.hashesShift;
                miner.connectTimeShift = Date.now();
                miner.hashesShift = miner.hashes;
            }
        } else {
            miner.connectTimeShift = Date.now();
            miner.hashesShift = miner.hashes;
        }

        let hashes = miner.hashes;
        let period = (Date.now() - miner.connectTime) / 1000;

        if (hashes === 0) {
            hashes = this.difficulty;
            target = 2 * global.config.pool.retargetTime;
            if (period < target) period = target;
        }
        const diff = Math.floor(hashes * target / period);
        return diff < min_diff ? min_diff : diff;
    };

    this.setNewDiff = function (difficulty) {
        if (this.fixed_diff) return false;

        let newDiff = Math.round(difficulty);
        if (newDiff > global.config.pool.maxDifficulty) {
            newDiff = global.config.pool.maxDifficulty;
        }
        if (newDiff < global.config.pool.minDifficulty) {
            newDiff = global.config.pool.minDifficulty;
        }

        this.newDiffRecommendation = newDiff;
        const ratio = Math.abs(newDiff - this.difficulty) / this.difficulty;
        if (ratio < 0.2) return false;
        this.newDiffToSet = newDiff;

        debug(threadName + "Difficulty change to: " + this.newDiffToSet + " For: " + this.logString);
        if (this.hashes > 0) {
            debug(threadName + "Hashes: " + this.hashes + " in: " + Math.floor((Date.now() - this.connectTime) / 1000) + " seconds gives: " +
                Math.floor(this.hashes / (Math.floor((Date.now() - this.connectTime) / 1000))) + " hashes/second or: " +
                Math.floor(this.hashes / (Math.floor((Date.now() - this.connectTime) / 1000))) * global.config.pool.targetTime + " difficulty versus: " + this.newDiffToSet);
        }
        return true;
    };

    this.checkBan = function (validShare) {
        if (!global.config.pool.banEnabled) return;

        // Valid stats are stored by the pool.
        if (validShare) {
          ++ this.validShares;
        } else {
          if (this.validShares === 0) {
            console.error(threadName + "Suspended miner IP for submitting bad share with zero trust " + this.logString);
            removeMiner(this);
            process.send({type: 'banIP', data: this.ipAddress});
            return;
          }
          ++ this.invalidShares;
        }

        const shareCount = this.validShares + this.invalidShares;
        if (shareCount >= global.config.pool.banThreshold) {
            if (100 * this.invalidShares / shareCount >= global.config.pool.banPercent) {
                console.error(threadName + "Suspended miner IP for submitting too many bad shares recently " + this.logString);
                removeMiner(this);
                process.send({type: 'banIP', data: this.ipAddress});
            } else {
                this.invalidShares = 0;
                this.validShares   = 0;
            }
        }
    };

    if (protoVersion === 1) {
        this.getCoinJob = function (coin, params) {
            const bt = params.bt;
            if (this.jobLastBlockHash === bt.idHash && !this.newDiffToSet && this.cachedJob !== null) return null;
            this.jobLastBlockHash = bt.idHash;

            if (this.newDiffToSet) {
                this.difficulty            = this.newDiffToSet;
                this.newDiffToSet          = null;
                this.newDiffRecommendation = null;
            } else if (this.newDiffRecommendation) {
                this.difficulty            = this.newDiffRecommendation;
                this.newDiffRecommendation = null;
            }

            const blob_type_num = global.coinFuncs.portBlobType(bt.port);

            if (!this.proxy) {
                const blob   = bt.nextBlob();
                const newJob = {
                    id:             crypto.pseudoRandomBytes(21).toString('base64'),
                    coin:           coin,
                    blob_type_num:  blob_type_num,
                    blockHash:      bt.idHash,
                    extraNonce:     bt.extraNonce,
                    height:         bt.height,
                    seed_hash:      bt.seed_hash,
                    difficulty:     this.difficulty,
                    coinHashFactor: params.coinHashFactor,
                    submissions:    {}
                };
                this.validJobs.enq(newJob);
                this.cachedJob = {
                    blob:      blob,
                    algo:      params.algo_name,
                    //variant:   params.variant_name,
                    height:    bt.height,
                    seed_hash: bt.seed_hash,
                    job_id:    newJob.id,
                    target:    getTargetHex(this.difficulty, blob_type_num == 7 ? 8 : 4),
                    id:        this.id
                };
            } else {
                const blob   = bt.nextBlobWithChildNonce();
                const newJob = {
                    id:                  crypto.pseudoRandomBytes(21).toString('base64'),
                    coin:                coin,
                    blob_type_num:       blob_type_num,
                    blockHash:           bt.idHash,
                    extraNonce:          bt.extraNonce,
                    height:              bt.height,
                    seed_hash:           bt.seed_hash,
                    difficulty:          this.difficulty,
                    clientPoolLocation:  bt.clientPoolLocation,
                    clientNonceLocation: bt.clientNonceLocation,
                    coinHashFactor:      params.coinHashFactor,
                    submissions:         {}
                };
                this.validJobs.enq(newJob);
                this.cachedJob = {
                    blocktemplate_blob:  blob,
                    blob_type:           global.coinFuncs.blobTypeStr(bt.port, bt.buffer[0]),
                    algo:                params.algo_name,
                    //variant:             params.variant_name,
                    difficulty:          bt.difficulty,
                    height:              bt.height,
                    seed_hash:           bt.seed_hash,
                    reserved_offset:     bt.reserved_offset,
                    client_nonce_offset: bt.clientNonceLocation,
                    client_pool_offset:  bt.clientPoolLocation,
                    target_diff:         this.difficulty,
                    job_id:              newJob.id,
                    id:                  this.id
                };
            }
            return this.cachedJob;
        };

        this.sendCoinJob = function(coin, params) {
            const job = this.getCoinJob(coin, params);
            if (job === null) return;
            return this.messageSender('job', job);
        };

        this.sendSameCoinJob = function () {
            const coin = typeof(this.curr_coin) !== 'undefined' ? this.curr_coin : this.selectBestCoin()
            return this.sendCoinJob(coin, getCoinJobParams(coin));
        };

        this.getBestCoinJob = function() {
            const coin = this.selectBestCoin();
            return this.getCoinJob(coin, getCoinJobParams(coin));
        };

        this.sendBestCoinJob = function() {
            const coin = this.selectBestCoin();
            return this.sendCoinJob(coin, getCoinJobParams(coin));
        };
    }
}

function recordShareData(miner, job, shareDiff, isBlockCandidate, hashHex, isTrustedShare, blockTemplate) {
    miner.hashes += job.difficulty;
    // transform it
    var share = {
        difficulty: job.difficulty,
        networkDifficulty: activeBlockTemplate.difficulty,
        blockHeight: job.height,
        blockReward: undefined, // filled during unlock
        miner: miner.address,
        worker: miner.identifier,
        ipAddress: miner.ipAddress,
        isBlockCandidate: blockCandidate,
        transactionConfirmationData: hashHex,
        blockHash: hashHex,
        userAgent: miner.agent,
        payoutInfo: miner.paymentID, // monero only
        source: global.config.clusterName
    };

    const rawMsg = config.publisherJson ? JSON.stringify(share) :
        Buffer.from(ShareMessage.encode(ShareMessage.create(share)).finish());

    // publish
    pubSock.send([config.publisherTopic, pubFlagsBuf, rawMsg]);

    if (shareType) {
        // process.send({type: 'trustedShare'});
        debug("Accepted trusted share at difficulty: " + job.difficulty + "/" + shareDiff + " from: " + miner.logString);
    } else {
        // process.send({type: 'normalShare'});
        debug("Accepted valid share at difficulty: " + job.difficulty + "/" + shareDiff + " from: " + miner.logString);
    }
}

function getShareBuffer(miner, job, blockTemplate, params) {
    try {
        let template = new Buffer(blockTemplate.buffer.length);
        blockTemplate.buffer.copy(template);
        template.writeUInt32BE(job.extraNonce, blockTemplate.reserved_offset);
        if (miner.proxy) {
            template.writeUInt32BE(params.poolNonce,   job.clientPoolLocation);
            template.writeUInt32BE(params.workerNonce, job.clientNonceLocation);
        }
        return global.coinFuncs.constructNewBlob(template, new Buffer(params.nonce, 'hex'), blockTemplate.port);
    } catch (e) {
        const err_str = "Can't constructNewBlob with " + params.nonce + " nonce from " + miner.logString + ": " + e;
        console.error(err_str);
        global.support.sendEmail(global.config.general.adminEmail, "FYI: Can't constructNewBlob", err_str);
        return null;
    }
}


function invalid_share(miner) {
    process.send({type: 'invalidShare'});
    miner.sendSameCoinJob();
    walletTrust[miner.payout] = 0;
    return false;
}

function submit_block(miner, job, blockTemplate, shareBuffer, resultHash, hashDiff, isTrustedShare, isParentBlock, isRetrySubmitBlock) {
    global.support.rpcPortDaemon(blockTemplate.port, 'submitblock', [shareBuffer.toString('hex')], function (rpcResult) {
        if (rpcResult.error) {
            // Did not manage to submit a block.  Log and continue on.
            recordShareData(miner, job, hashDiff.toString(), false, null, isTrustedShare, blockTemplate);
            let isNotifyAdmin = true;
            if (isParentBlock && isTrustedShare) {
                const convertedBlob = global.coinFuncs.convertBlob(shareBuffer, blockTemplate.port);
                const hash = global.coinFuncs.cryptoNight(convertedBlob, blockTemplate);
                if (hash.toString('hex') !== resultHash) isNotifyAdmin = false;
            }

            console.error(threadName + "Error submitting " + blockTemplate.coin + " (port " + blockTemplate.port + ") block at height " +
                blockTemplate.height + " (active block template height: " + activeBlockTemplates[blockTemplate.coin].height + ") from " +
                miner.logString + ", isTrustedShare: " + isTrustedShare + ", valid: " + isNotifyAdmin + " error: " + JSON.stringify(rpcResult.error) +
                ", block hex: \n" + shareBuffer.toString('hex')
            );

            if (isNotifyAdmin) setTimeout(function() { // only alert if block height is not changed in the nearest time
                global.coinFuncs.getPortLastBlockHeader(blockTemplate.port, function(err, body) {
                    if (err !== null) {
                        console.error("Last block header request failed for " + blockTemplate.port + " port!");
                        return;
                    }
                    if (blockTemplate.height == body.height + 1) global.support.sendEmail(global.config.general.adminEmail,
                        "FYI: Can't submit " + blockTemplate.coin + " block to deamon on " + blockTemplate.port + " port",
                        "The pool server: " + global.config.hostname + " can't submit block to deamon on " + blockTemplate.port + " port\n" +
                        "Input: " + shareBuffer.toString('hex') + "\n" +
                        threadName + "Error submitting " + blockTemplate.coin + " block at " + blockTemplate.height + " height from " + miner.logString +
                        ", isTrustedShare: " + isTrustedShare + " error: " + JSON.stringify(rpcResult.error)
                    );
               });
            }, 2*1000);

            if (global.config.pool.trustedMiners) {
                debug(threadName + "Share trust broken by " + miner.logString);
                miner.trust.trust         = 0;
                walletTrust[miner.payout] = 0;
            }
        } else if (rpcResult && typeof(rpcResult.result) !== 'undefined') {
            // Success! Submitted a block without an issue.
            const blockFastHash = global.coinFuncs.getBlockID(shareBuffer, blockTemplate.port).toString('hex');
            console.log(threadName + "New " + blockTemplate.coin + " (port " + blockTemplate.port + ") block " + blockFastHash + " found at height " + blockTemplate.height + " by " + miner.logString +
                ", isTrustedShare: " + isTrustedShare + " - submit result: " + JSON.stringify(rpcResult.result) +
                ", block hex: \n" + shareBuffer.toString('hex')
            );
            recordShareData(miner, job, hashDiff.toString(), true, blockFastHash, isTrustedShare, blockTemplate);
        } else {
            if (isRetrySubmitBlock) {
                setTimeout(submit_block, 500, miner, job, blockTemplate, shareBuffer, resultHash, hashDiff, isTrustedShare, isParentBlock, false);
            } else {
                // RPC bombed out massively.
                console.error(threadName + "RPC Error. Please check logs for details");
                global.support.sendEmail(global.config.general.adminEmail,
                    "FYI: Can't submit block to deamon on " + blockTemplate.port + " port",
                    "Input: " + shareBuffer.toString('hex') + "\n" +
                    "The pool server: " + global.config.hostname + " can't submit block to deamon on " + blockTemplate.port + " port\n" +
                    "RPC Error. Please check logs for details"
                );
            }
        }
    });
}

function processShare(miner, job, blockTemplate, params) {
    let hash;
    let isTrustedShare;
    let shareBuffer;
    const resultHash = params.result;

    if (miner.payout in minerWallets) minerWallets[miner.payout].hashes += job.difficulty;
    walletLastSeeTime[miner.payout] = Date.now();

    if (global.config.pool.trustedMiners &&
        is_safe_to_trust(job.rewarded_difficulty2, miner.payout, miner.trust.trust) &&
        miner.trust.check_height !== job.height
    ) {
        try {
            hash = new Buffer(resultHash, 'hex');
            if (miner.payout in extra_wallet_verify) {
                shareBuffer = getShareBuffer(miner, job, blockTemplate, params);
                if (shareBuffer !== null) {
                    let convertedBlob = global.coinFuncs.convertBlob(shareBuffer, blockTemplate.port);
                    const hash2 = global.coinFuncs.cryptoNight(convertedBlob, blockTemplate);
                    if (hash2.toString('hex') !== resultHash) {
                        console.error("EXTRA WALLET VERIFY " + miner.payout + ": INVALID SHARE OF " + job.rewarded_difficulty2 + " REWARD HASHES");
                    } else {
                        extra_verify_wallet_hashes.push(miner.payout + " " + convertedBlob.toString('hex') + " " + resultHash + " " + global.coinFuncs.algoShortTypeStr(blockTemplate.port) + " " + blockTemplate.height + " " + blockTemplate.seed_hash);
                    }
                } else {
                    console.error("EXTRA WALLET VERIFY " + miner.payout + ": CAN'T MAKE SHARE BUFFER");
                }
            }
        } catch (err) {
            return invalid_share(miner);
        }
        isTrustedShare = true;
    } else { // verify share
        if (miner.debugMiner) console.log(threadName + miner.logString + ": verify share");
        if (miner.payout in minerWallets && ++minerWallets[miner.payout].last_ver_shares >= MAX_VER_SHARES_PER_SEC * VER_SHARES_PERIOD) {
            if (minerWallets[miner.payout].last_ver_shares === MAX_VER_SHARES_PER_SEC * VER_SHARES_PERIOD) {
                console.error(threadName + "Throttled down miner share (diff " + job.rewarded_difficulty2 + ") submission from " + miner.logString);
            }
            process.send({type: 'throttledShare'});
            addProxyMiner(miner);
            const proxyMinerName = miner.payout + ":" + miner.identifier;
            proxyMiners[proxyMinerName].hashes += job.difficulty;
            adjustMinerDiff(miner);
            return null;
        }
        shareBuffer = getShareBuffer(miner, job, blockTemplate, params);
        if (shareBuffer === null) return invalid_share(miner);
        let convertedBlob = global.coinFuncs.convertBlob(shareBuffer, blockTemplate.port);
        hash = global.coinFuncs.cryptoNight(convertedBlob, blockTemplate);

        if (hash.toString('hex') !== resultHash) {
            let time_now = Date.now();
            if (!(miner.payout in lastMinerLogTime) || time_now - lastMinerLogTime[miner.payout] > 30*1000) {
                console.error(threadName + "Bad share from miner (diff " + job.difficulty + ") " + miner.logString);
                lastMinerLogTime[miner.payout] = time_now;
            }
            return invalid_share(miner);
        }

        walletTrust[miner.payout] += job.rewarded_difficulty2;
        isTrustedShare = false;
    }

    let hashArray = hash.toByteArray().reverse();
    let hashNum   = bignum.fromBuffer(new Buffer(hashArray));
    let hashDiff  = baseDiff.div(hashNum);

    let is_block_diff_matched = false;

    if (hashDiff.ge(blockTemplate.difficulty)) { // Submit block to the RPC Daemon.
        if (!shareBuffer) {
            shareBuffer = getShareBuffer(miner, job, blockTemplate, params);
            if (!shareBuffer) return invalid_share(miner);
        }
        submit_block(miner, job, blockTemplate, shareBuffer, resultHash, hashDiff, isTrustedShare, true, true);
        is_block_diff_matched = true;
    }

    const is_mm = "child_template" in blockTemplate;
    if (is_mm && hashDiff.ge(blockTemplate.child_template.difficulty)) { // Submit child block to the RPC Daemon.
        if (!shareBuffer) {
            shareBuffer = getShareBuffer(miner, job, blockTemplate, params);
            if (!shareBuffer) return invalid_share(miner);
        }
        // need to properly restore child template buffer here since it went via message string and was restored not correctly
        blockTemplate.child_template_buffer = Buffer.from(blockTemplate.child_template_buffer);
        let shareBuffer2 = null;
        try {
            shareBuffer2 = global.coinFuncs.constructMMChildBlockBlob(shareBuffer, blockTemplate.port, blockTemplate.child_template_buffer);
        } catch (e) {
            const err_str = "Can't construct_mm_child_block_blob with " + shareBuffer.toString('hex') + " parent block and " + blockTemplate.child_template_buffer.toString('hex') + " child block share buffers from " + miner.logString + ": " + e;
            console.error(err_str);
            global.support.sendEmail(global.config.general.adminEmail, "FYI: Can't construct_mm_child_block_blob", err_str);
            return invalid_share(miner);
        }
        if (shareBuffer2 === null) return invalid_share(miner);
        submit_block(miner, job, blockTemplate.child_template, shareBuffer2, resultHash, hashDiff, isTrustedShare, false, true);
        is_block_diff_matched = true;
    }

    if (is_block_diff_matched) { // Do nothing here

    } else if (hashDiff.lt(job.difficulty)) {
        let time_now = Date.now();
        if (!(miner.payout in lastMinerLogTime) || time_now - lastMinerLogTime[miner.payout] > 30*1000) {
           console.warn(threadName + "Rejected low diff (" + hashDiff.toString() + " < " + job.difficulty + ") share from miner " + miner.logString);
           lastMinerLogTime[miner.payout] = time_now;
        }
        return invalid_share(miner);

    } else {
        recordShareData(miner, job, hashDiff.toString(), false, null, isTrustedShare, blockTemplate);
        // record child proc share for rewarded_difficulty effort calcs status but with 0 rewards (all included in parent share)
        if (is_mm) {
            job.rewarded_difficulty2 = 0;
            recordShareData(miner, job, hashDiff.toString(), false, null, isTrustedShare, blockTemplate.child_template);
        }
    }

    return true;
}

// Message times for different miner addresses
let lastMinerLogTime = {};
// Miner notification times
let lastMinerNotifyTime = {};

function get_miner_notification(payout) {
    if (payout in notifyAddresses) return notifyAddresses[payout];
    return false;
}

function handleMinerData(method, params, ip, portData, sendReply, sendFinalReply, pushMessage) {
    let miner;
    switch (method) {
        case 'login':
            if (ip in bannedIPs) {
                sendFinalReply("New connections from this IP address are temporarily suspended from mining (10 minutes max)");
                return;
            }
            if (!params.login) {
                sendFinalReply("No login specified");
                return;
            }
            if (!params.pass) params.pass = "x";
            let difficulty = portData.difficulty;
            let minerId = uuidV4();
            miner = new Miner(
                minerId, params.login, params.pass, ip, difficulty, pushMessage, 1, portData.portType, portData.port, params.agent,
                params.algo, params["algo-perf"], params["algo-min-time"]
            );
            if (params.agent && cluster.worker.id == 1) minerAgents[params.agent] = 1;
            let time_now = Date.now();
            if (!miner.valid_miner) {
                if (!(miner.payout in lastMinerLogTime) || time_now - lastMinerLogTime[miner.payout] > 10*60*1000) {
                    console.log("Invalid miner " + miner.logString + " [" + miner.email + "], disconnecting due to: " + miner.error);
                    lastMinerLogTime[miner.payout] = time_now;
                }
                sendFinalReply(miner.error);
                return;
            }

            if (global.coinFuncs.algoMainCheck(miner.algos)) {
                let miner_agent_notification = params.agent ? global.coinFuncs.get_miner_agent_notification(params.agent) : false;
                let miner_notification = miner_agent_notification ? miner_agent_notification : global.coinFuncs.get_miner_agent_warning_notification(params.agent);
                miner_notification = miner_notification ? miner_notification : get_miner_notification(miner.payout);
                if (miner_notification) {
                    if (!(miner.payout in lastMinerNotifyTime) || time_now - lastMinerNotifyTime[miner.payout] > 60*60*1000) {
                        lastMinerNotifyTime[miner.payout] = time_now;
                        console.error("Sent notification to " + miner.logString + ": " + miner_notification);
                        sendFinalReply(miner_notification + " (miner will connect after several attempts)");
                        return;
                    }
                }
                if (miner_agent_notification) {
                    if (!(miner.payout in lastMinerNotifyTime) || time_now - lastMinerNotifyTime[miner.payout] > 60*60*1000) {
                        lastMinerNotifyTime[miner.payout] = time_now;
                        console.error("Sent notification to " + miner.logString + ": " + miner_agent_notification);
                    }
                    sendFinalReply(miner_agent_notification);
                    return;
                }
            }

            activeMiners.set(minerId, miner);

            if (!miner.proxy) {
                let proxyMinerName = miner.payout + ":" + miner.identifier;
                if ((params.agent && params.agent.includes('proxy')) || (proxyMinerName in proxyMiners)) {
                    addProxyMiner(miner);
                    if (proxyMiners[proxyMinerName].hashes) adjustMinerDiff(miner);
                } else {
                    if (!(miner.payout in minerWallets)) {
                        minerWallets[miner.payout] = {};
                        minerWallets[miner.payout].connectTime = Date.now();
                        minerWallets[miner.payout].count = 1;
                        minerWallets[miner.payout].hashes = 0;
                        minerWallets[miner.payout].last_ver_shares = 0;
                    } else {
                        ++ minerWallets[miner.payout].count;
                    }
                }
            }
            sendReply(null, {
                id: minerId,
                job: miner.getBestCoinJob(),
                status: 'OK'
            });
            break;
        case 'getjob':
            miner = activeMiners.get(params.id);
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            if (params.algo && params.algo instanceof Array && params["algo-perf"] && params["algo-perf"] instanceof Object) {
                const status = miner.setAlgos(params.algo, params["algo-perf"], params["algo-min-time"]);
                if (status != "") {
                    sendReply(status);
                    return;
                }
            }
            miner.sendBestCoinJob();
            break;
        case 'submit':
            miner = activeMiners.get(params.id);
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            //if (miner.debugMiner) console.log("SUBMIT");
            miner.heartbeat();

            let job = miner.validJobs.toarray().filter(function (job) {
                return job.id === params.job_id;
            })[0];

            if (!job) {
                sendReply('Invalid job id');
                return;
            }

            const nonceCheck = job.blob_type_num == 7 ? nonceCheck64 : nonceCheck32;

            if ((typeof params.nonce !== 'string') || !nonceCheck.test(params.nonce)) {
                console.warn(threadName + 'Malformed nonce: ' + JSON.stringify(params) + ' from ' + miner.logString);
                miner.checkBan(false);
                sendReply('Duplicate share');
                miner.storeInvalidShare();
                return;
            }

            let nonce_test;
            if (miner.proxy) {
                if (!Number.isInteger(params.poolNonce) || !Number.isInteger(params.workerNonce)) {
                    console.warn(threadName + 'Malformed nonce: ' + JSON.stringify(params) + ' from ' + miner.logString);
                    miner.checkBan(false);
                    sendReply('Duplicate share');
                    miner.storeInvalidShare();
                    return;
                }
                nonce_test = `${params.nonce}_${params.poolNonce}_${params.workerNonce}`;
            } else {
                nonce_test = params.nonce;
            }

            if (nonce_test in job.submissions) {
                console.warn(threadName + 'Duplicate miner share with ' + nonce_test + ' nonce from ' + miner.logString);
                miner.checkBan(false);
                sendReply('Duplicate share');
                miner.storeInvalidShare();
                return;
            }
            job.submissions[nonce_test] = 1;

            let blockTemplate;
            job.rewarded_difficulty = job.difficulty;

            if (activeBlockTemplates[job.coin].idHash !== job.blockHash) {
                blockTemplate = pastBlockTemplates[job.coin].toarray().filter(function (t) {
                    return t.idHash === job.blockHash;
                })[0];
                let is_outdated = false;
                if (blockTemplate && blockTemplate.timeOutdate) {
                    const late_time = Date.now() - blockTemplate.timeOutdate;
                    if (late_time > 0) {
                        const max_late_time = global.config.pool.targetTime*1000;
                        if (late_time < max_late_time) {
                            let factor = (max_late_time - late_time) / max_late_time;
                            job.rewarded_difficulty = Math.floor(job.difficulty * Math.pow(factor, 6));
                            if (job.rewarded_difficulty === 0) job.rewarded_difficulty = 1;
                        } else {
                            is_outdated = true;
                        }
                    }
                }
                if (!blockTemplate || is_outdated) {
                    let err_str = is_outdated ? "Block outdated" : "Block expired";
                    let time_now = Date.now();
                    if (!(miner.payout in lastMinerLogTime) || time_now - lastMinerLogTime[miner.payout] > 30*1000) {
                        console.warn(threadName + err_str + ', Height: ' + job.height + ' (diff ' + job.difficulty + ') from ' + miner.logString);
                        lastMinerLogTime[miner.payout] = time_now;
                    }
                    miner.sendSameCoinJob();
                    sendReply(err_str);
                    miner.storeInvalidShare();
                    return;
                }
            } else {
                blockTemplate = activeBlockTemplates[job.coin];
            }

            job.rewarded_difficulty2 = job.rewarded_difficulty * job.coinHashFactor;

            let shareAccepted = processShare(miner, job, blockTemplate, params);
            if (shareAccepted === null) {
                sendReply('Throttled down share submission (please use high fixed diff or use xmr-node-proxy)');
                return;
            }
            miner.checkBan(shareAccepted);

            if (global.config.pool.trustedMiners) {
                if (shareAccepted) {
                    miner.trust.trust += job.rewarded_difficulty2;
                    miner.trust.check_height = 0;
                } else {
                    debug(threadName + "Share trust broken by " + miner.logString);
                    miner.storeInvalidShare();
                    miner.trust.trust = 0;
                }
            }

            if (!shareAccepted) {
                sendReply('Low difficulty share');
                return;
            }

            miner.lastShareTime = Date.now() / 1000 || 0;

            sendReply(null, {status: 'OK'});
            //if (miner.debugMiner) console.log("SUBMIT OK");
            break;
        case 'keepalived':
            miner = activeMiners.get(params.id);
            if (!miner) {
                sendReply('Unauthenticated');
                return;
            }
            miner.heartbeat();
            sendReply(null, {
                status: 'KEEPALIVED'
            });
            break;
    }
}

if (global.config.general.allowStuckPoolKill && fs.existsSync("block_template_is_stuck")) {
   console.error("Stuck block template was detected on previous run. Please fix monerod and remove block_template_is_stuck file after that. Exiting...");
   setTimeout(function() { process.exit(); }, 5*1000);
   return;
}

setInterval(function dump_vars() {
   const fn = "dump" + (cluster.isMaster ? "" : "_" + cluster.worker.id.toString());
   fs.access(fn, fs.F_OK, function(err) {
      if (!err) return;
      console.log("DUMPING VARS TO " + fn + " FILE");
      let s = fs.createWriteStream(fn, {'flags': 'a'});

      s.write("activeMiners:\n");
      for (var [minerId, miner] of activeMiners) s.write(minerId + ": " + JSON.stringify(miner, null, '\t') + "\n");

      s.write("\n\n\npastBlockTemplates:\n");
      s.write(JSON.stringify(pastBlockTemplates, null, '\t') + "\n");

      s.write("\n\n\nlastBlockHash:\n");
      s.write(JSON.stringify(lastBlockHash, null, '\t') + "\n");

      s.write("\n\n\nlastCoinHashFactor:\n");
      s.write(JSON.stringify(lastCoinHashFactor, null, '\t') + "\n");

      s.write("\n\n\ncurrCoinHashFactor:\n");
      s.write(JSON.stringify(currCoinHashFactor, null, '\t') + "\n");

      s.write("\n\n\ncurrCoinHashFactorMM:\n");
      s.write(JSON.stringify(currCoinHashFactorMM, null, '\t') + "\n");

      s.write("\n\n\nactiveBlockTemplates:\n");
      s.write(JSON.stringify(activeBlockTemplates, null, '\t') + "\n");

      s.write("\n\n\nanchorBlockHeight: " + anchorBlockHeight + "\n");
      s.write("\n\n\nanchorBlockPrevHeight: " + anchorBlockPrevHeight + "\n");

      s.write("\n\n\nwalletTrust:\n");
      s.write(JSON.stringify(walletTrust, null, '\t') + "\n");

      s.write("\n\n\nwalletLastSeeTime:\n");
      s.write(JSON.stringify(walletLastSeeTime, null, '\t') + "\n");

      s.write("\n\n\nwalletAcc:\n");
      s.write(JSON.stringify(walletAcc, null, '\t') + "\n");

      s.write("\n\n\nwalletWorkerCount:\n");
      s.write(JSON.stringify(walletWorkerCount, null, '\t') + "\n");

      s.write("\n\n\nis_walletAccFinalizer:\n");
      s.write(JSON.stringify(is_walletAccFinalizer, null, '\t') + "\n");

      s.end();
   });
}, 60*1000);

if (cluster.isMaster) {
    const numWorkers = require('os').cpus().length;
    for (let i = 1; i <= numWorkers; ++ i) {
        minerCount[i] = [];
        Object.keys(global.config.ports).forEach(function (port) {
            minerCount[i][port] = 0;
        });
    }
    console.log('Master cluster setting up ' + numWorkers + ' workers...');

    for (let i = 0; i < numWorkers; i++) {
        let worker = cluster.fork();
        worker.on('message', messageHandler);
    }

    cluster.on('online', function (worker) {
        console.log('Worker ' + worker.process.pid + ' is online');
    });

    cluster.on('exit', function (worker, code, signal) {
        console.error('Worker ' + worker.process.pid + ' died with code: ' + code + ', and signal: ' + signal);
        console.log('Starting a new worker');
        worker = cluster.fork();
        worker.on('message', messageHandler);
        console.log(global.config.general.adminEmail, "FYI: Started new worker " + worker.id,
            "Hello,\r\nMaster thread of " + global.config.hostname + " starts new worker with id " + worker.id);
    });


    if (!global.config.daemon.activePort) {
        console.warn("global.config.daemon.activePort is not defined, using fixed global.config.daemon.port instead");
        global.config.daemon.activePort = global.config.daemon.port;
    } else {
        currCoinHashFactor[""] = currCoinHashFactorMM[""] = 1;
        setInterval(updateActivePort, 3*1000, "");
        if (global.config.daemon.enableAlgoSwitching) COINS.forEach(function(coin) {
            currCoinHashFactor[coin] = currCoinHashFactorMM[coin] = 0;
            if ("activePort" + coin in global.config.daemon) {
                setInterval(updateActivePort, 5*1000, coin);
                templateUpdate(coin);
                setTimeout(templateUpdate, 50, coin, true);
            } else {
                console.warn("global.config.daemon." + "activePort" + coin + " is not defined, so ignoring its coin changes");
            }
        });
    }

    templateUpdate("");
    setTimeout(templateUpdate, 50, "", true);
    console.log("Pool server online");

} else {
    currCoinHashFactor[""] = currCoinHashFactorMM[""] = 1;
    templateUpdate("");
    if (global.config.daemon.enableAlgoSwitching) COINS.forEach(function(coin) {
        currCoinHashFactor[coin] = currCoinHashFactorMM[coin] = 0;
        if ("activePort" + coin in global.config.daemon) templateUpdate(coin);
    });
    anchorBlockUpdate();
    setInterval(anchorBlockUpdate, 3*1000);
    setInterval(checkAliveMiners, 60*1000);
    setInterval(retargetMiners, global.config.pool.retargetTime * 1000);
    setInterval(function () {
        bannedIPs = {};
    }, 10*60*1000);

    let lastGarbageFromIpTime = {};

    async.each(Object.keys(global.config.ports), function (port) {
        const portData = global.config.ports[port];

        let handleMessage = function (socket, jsonData, pushMessage) {
            if (!jsonData.id) {
                console.warn('Miner RPC request missing RPC id');
                return;
            }
            else if (!jsonData.method) {
                console.warn('Miner RPC request missing RPC method');
                return;
            }
            else if (!jsonData.params) {
                console.warn('Miner RPC request missing RPC params');
                return;
            }

            let sendReply = function (error, result) {
                if (!socket.writable) {
                    return;
                }
                let sendData = JSON.stringify({
                        id: jsonData.id,
                        jsonrpc: "2.0",
                        error: error ? {code: -1, message: error} : null,
                        result: result
                    }) + "\n";
                socket.write(sendData);
            };
            let sendFinalReply = function (error) {
                setTimeout(function() {
                  socket.end(JSON.stringify({
                    id: jsonData.id,
                    jsonrpc: "2.0",
                    error: {code: -1, message: error},
                    result: null
                  }) + "\n");
                }, 9 * 1000);
            };
            handleMinerData(jsonData.method, jsonData.params, socket.remoteAddress, portData, sendReply, sendFinalReply, pushMessage);
        };

        function socketConn(socket) {
            socket.setKeepAlive(true);
            socket.setEncoding('utf8');

            let dataBuffer = '';

            let pushMessage = function (method, params) {
                if (!socket.writable) {
                    return;
                }
                let sendData = JSON.stringify({
                        jsonrpc: "2.0",
                        method: method,
                        params: params
                    }) + "\n";
                socket.write(sendData);
            };

            socket.on('data', function (d) {
                dataBuffer += d;
                if (Buffer.byteLength(dataBuffer, 'utf8') > 102400) { //100KB
                    dataBuffer = null;
                    console.warn(threadName + 'Excessive packet size from: ' + socket.remoteAddress);
                    socket.destroy();
                    return;
                }
                if (dataBuffer.indexOf('\n') !== -1) {
                    let messages = dataBuffer.split('\n');
                    let incomplete = dataBuffer.slice(-1) === '\n' ? '' : messages.pop();
                    for (let i = 0; i < messages.length; i++) {
                        let message = messages[i];
                        if (message.trim() === '') {
                            continue;
                        }
                        let jsonData;
                        try {
                            jsonData = JSON.parse(message);
                        }
                        catch (e) {
                            if (message.indexOf('GET /') === 0) {
                                if (message.indexOf('HTTP/1.1') !== -1) {
                                    socket.end('HTTP/1.1' + httpResponse);
                                    break;
                                }
                                else if (message.indexOf('HTTP/1.0') !== -1) {
                                    socket.end('HTTP/1.0' + httpResponse);
                                    break;
                                }
                            }

                            let time_now = Date.now();
                            if (!(socket.remoteAddress in lastGarbageFromIpTime) || time_now - lastGarbageFromIpTime[socket.remoteAddress] > 60*1000) {
                                console.warn(threadName + "Malformed message from " + socket.remoteAddress + " Message: " + JSON.stringify(message));
                                lastGarbageFromIpTime[socket.remoteAddress] = time_now;
                            }
                            socket.destroy();

                            break;
                        }
                        handleMessage(socket, jsonData, pushMessage);
                    }
                    dataBuffer = incomplete;
                }
            }).on('error', function (err) {
                debug(threadName + "Socket Error " + err.code + " from " + socket.remoteAddress + " Error: " + err);
            }).on('close', function () {
                pushMessage = function () {
                };
            });
        }

        if ('ssl' in portData && portData.ssl === true) {
            let server = tls.createServer({
                key: fs.readFileSync('cert.key'),
                cert: fs.readFileSync('cert.pem')
            }, socketConn);
            server.listen(portData.port, global.config.bind_ip, function (error) {
                if (error) {
                    console.error(threadName + "Unable to start server on: " + portData.port + " Message: " + error);
                    return;
                }
                console.log(threadName + "Started server on port: " + portData.port);
            });
            server.on('error', function (error) {
                console.error("Can't bind server to " + portData.port + " SSL port!");
            });
        } else {
            let server = net.createServer(socketConn);
            server.listen(portData.port, global.config.bind_ip, function (error) {
                if (error) {
                    console.error(threadName + "Unable to start server on: " + portData.port + " Message: " + error);
                    return;
                }
                console.log(threadName + "Started server on port: " + portData.port);
            });
            server.on('error', function (error) {
                console.error("Can't bind server to " + portData.port + " port!");
            });
        }
    });
}
