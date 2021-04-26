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

const sub_name = v => "Sub_" + v;

const buf =
  "%HES\n" +
  "S =v\n" +
  vars.map(v => "∀" + v + ".").join(" ") + "\n" +
  vars.map(v => v + " <= 0").join(" \\/ ") + " \\/\n" +
  "(" +
  "∀r1." +
  vars.map(v => "r1 < 1 + " + v).join(" \\/ ") + " \\/\n" +
  (omit_minus ? "" : vars.map(v => "r1 < 1 - " + v).join(" \\/ ") + " \\/\n") +
  "Main r1 " + vars.map(v => v).join(" ") +
  " (\\k. true)" +
  ").\n\n" +
  "Main r1 " + vars.map(v => v).join(" ") + " k =v\n" +
  "r1 > 0 /\\\n" +
  "(x1 > 0 \\/ k false) /\\\n(x1 <= 0 \\/\n" +
  vars.map(v =>
    "(∀rr. " +
      "rr < 1 + " + v + " \\/ " +
      "rr < 1 - " + v + " \\/ " +
      sub_name(v) + " rr " + v + ")").join(" /\\\n") + " /\\\n" +
  "Main (r1 - 1) " +
  "(x1 - 1) " + vars.slice(1).map(v => v).join(" ") +
  " k).\n\n" +
  vars.map(v => sub_name(v) + " r x =v r > 0 /\\ (x > 0 \\/ true) /\\ (x <= 0 \\/ " + sub_name(v) + " (r - 1) (x - 1)).").join("\n")
  ;
  
console.log(buf);
