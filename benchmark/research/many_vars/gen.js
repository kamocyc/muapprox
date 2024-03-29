// node benchmark/research/many_vars/gen.js > benchmark/research/many_vars/many_vars.in
// /opt/home2/git/hflmc2_mora/_build/default/bin/main.exe --solver=hoice benchmark/research/many_vars/many_vars.in > a.txt


if(process.argv[2] === undefined) throw new Error("specify the number of variables");
if(process.argv[3] === undefined) throw new Error("specify sign flag");

const omit_minus = parseInt(process.argv[3]) !== 0;

const max = parseInt(process.argv[2]);
let vars = [];
for(let i=1; i<=max; i++) {
  vars.push("x" + i);
}
const buf =
  "%HES\n" +
  "S =v\n" +
  vars.map(v => "∀" + v + ".").join(" ") + "\n" +
  vars.map(v => v + " <= 0").join(" \\/ ") + " \\/\n" +
  "(" +
  "∀r1." +
  vars.map(v => "r1 < 1 + " + v).join(" \\/ ") + " \\/\n" +
  (omit_minus ? "" : vars.map(v => "r1 < 1 - " + v).join(" \\/ ") + " \\/\n") +
  "A r1 " + vars.map(v => v).join(" ") +
  ").\n\n" +
  "A r1 " + vars.map(v => v).join(" ") + " =v\n" +
  "r1 > 0 /\\\n" +
  "(x1 > 0 \\/ true) /\\\n(x1 <= 0 \\/\n" +
  "A (r1 - 1) " +
  //"(x1 - 1) " + vars.slice(1).map(v => v).join(" ") +
  vars.map(v => "(" + v + " - 1)").join(" ") +
  ").\n";
  
console.log(buf);
