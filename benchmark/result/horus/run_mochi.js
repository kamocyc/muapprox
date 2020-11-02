#!/usr/bin/env node

const path = require('path');
const child_process = require('child_process');
const {performance} = require('perf_hooks');

// usage: node run_mochi.js MODE FILE
// MODE: "safety" or "nontermination"
const mode = process.argv[2];
const file = process.argv[3];

const conf = {
  safety: {
    command: "/home/rsuzuki/bin/mochi",
    options: [],
  },
  "non-termination": {
    command: "./mochi_nonterm_bin/mochi",
    options: ["-non-termination"],
  },
  horus: {
    command: "./horus_helper.sh",
    options: [],
  },
  "horus-cps": {
    command: "./horus_helper.sh",
    options: [],
  },
};

const currentConf = conf[mode];
if (currentConf == null) {
  throw new Error(`Unknown mode: ${mode}`);
}

// whether debug log is on.
const isDebugMode = false;

const timeout = parseInt(process.env.TIMEOUT, 10) || 10;

(async ()=> {
	const startTime = performance.now();
	const result = await runCommand(currentConf.command, [file], {
		env: {},
		timeout: timeout * 1000,
	}).catch(e => {
		if (e === 'TIMEOUT') {
			// timeout
			return 'timeout';
		} else {
			// error
			if (isDebugMode) {
				console.error(e);
			}
			return 'error';
		}
	});
	const endTime = performance.now();
	const dur = (endTime - startTime) / 1e3;

	const resultString = result || dur.toFixed(4);
	const basename = path.basename(file, path.extname(file));

	const logString = `${basename},${resultString}`;
	console.log(logString);
})();

function runCommand(command, args, {env, timeout}) {
    let ended = false;

    return new Promise((resolve, reject) => {
        const options = currentConf.options.concat(args);
        if (isDebugMode) {
            console.debug(command, options);
        }
        const child = child_process.spawn(command, options, {
            detached: true,
            env,
            stdio: ['ignore', 'ignore', 'pipe'],
        });
        const errorEnd = err => {
            if (!ended) {
                ended = true;
            }
            if (timerId != null) {
                clearTimeout(timerId);
            }
            reject(err);
            if (child.pid) {
                process.kill(-child.pid);
            }
        };
        child.stderr.on('data', (data) => {
          if (data.toString()==='sat\n' && (mode==='horus' || mode==='horus-cps')) {
            errorEnd('UNKNOWN')
          }
        });
        child.on('error', err=> {
            errorEnd(err);
        });
        child.on('exit', ()=> {
            if (!ended) {
                ended = true;
            }
            if (timerId != null) {
                clearTimeout(timerId);
            }
            resolve();
        });
        // invoke timer for timeout
        let timerId = setTimeout(()=> {
            timerId = null;
            errorEnd("TIMEOUT");
        }, timeout);
    });
}


