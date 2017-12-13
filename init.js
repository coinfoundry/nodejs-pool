"use strict";

// validate args
if(process.argv.length < 3) {
    console.log("Error: Config file argument required. Good bye ..");
    process.exit(1);
}

let fs = require("fs");
let config = fs.readFileSync(process.argv[2]);
let coinConfig = fs.readFileSync("./coinConfig.json");
let path = require('path');

global.support = require("./lib/support.js")();
global.config = JSON.parse(config);
let comms;
let coinInc;

global.config['coin'] = JSON.parse(coinConfig)[global.config.coin];
coinInc = require(global.config.coin.funcFile);
global.coinFuncs = new coinInc();

global.coinFuncs.blockedAddresses.push(global.config.pool.address);

require('./lib/pool.js');
