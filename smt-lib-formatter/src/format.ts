import * as sexp from 'sexp';

type Sexp = (Sexp | string)[];

// function removeComments(text: string): string {
//   return text.replace(/;.*$/g, '');
// }

export function format(text: string): string {
  // Currently, we cannot handle comments
  if(text.match(/;/) !== null) return text;
  
  const exp = sexp("(" + text + ")") as Sexp;
  const indentDepth = "  ";
  const singleLineFunctions = ['+', '-', '*', '/', '=', '>=', '<=', '>', '<'];
  
  // function get_depth(exp: Sexp): number {
  //   return exp.map(e => Array.isArray(e) ? (get_depth(e) + 1) : 0).reduce((c, e) => c < e ? e : c, 0);
  // }
  
  function format_inner2(exp: Sexp | string): string {
    if(!Array.isArray(exp)) return exp;
    
    return "(" + exp.map((s, i) => {
      if(Array.isArray(s)) {
        s = format_inner2(s);
      }
      
      return (i === 0 ? "" : " ") + s;
    }).join("") + ")";
  }
  
  function format_inner(exp: Sexp, indent: string): string {
    if(exp.length >= 1 && typeof exp[0] === 'string' && ["declare-fun", "declare-const"].indexOf(exp[0]) !== -1) {
      return format_inner2(exp);
    }
    if(exp.length >= 1 && typeof exp[0] === 'string' && ["exists", "forall"].indexOf(exp[0]) !== -1) {
      if(exp.length === 3 && Array.isArray(exp[1]) && Array.isArray(exp[2])) {
        return "(" + exp[0] + " " + format_inner2(exp[1]) + "\n" + indent + indentDepth + format_inner(exp[2], indent + indentDepth) + "\n" + indent + ")";
      }
    }
    if(exp.length === 5 && exp[0] === "define-fun") {
      return "(" + exp[0] + " " + format_inner2(exp[1]) + "\n" +
        indent + indentDepth + format_inner2(exp[2]) + " " + format_inner2(exp[3]) +
        (Array.isArray(exp[4]) ? ("\n" + indent + indentDepth + format_inner(exp[4], indent + indentDepth)) : " " + exp[4]) + "\n" + indent + ")";
    }
    if(exp.length >= 1 && typeof exp[0] === 'string' && singleLineFunctions.indexOf(exp[0]) !== -1/* && get_depth(exp) < 5*/) {
      // console.dir({exp, exp, depth: get_depth(exp)}, {depth: 10});
      return format_inner2(exp);
    }
    let contains_newline = false;
    return "(" +
      exp.map((s, i) => {
        if(Array.isArray(s)) {
          contains_newline = true;
          return "\n" + indent + indentDepth + format_inner(s, indent + indentDepth);
        } else {
          return (i === 0 ? "" : (Array.isArray(exp[i - 1]) ? ("\n" + indent + indentDepth) : " ")) + s;
        }
      }).join("") +
    (contains_newline ? ("\n" + indent) : "") +
    ")";
  }
  
  return exp.map(e => {
    return typeof e === "string" ? e : format_inner(e, "");
  }).join("\n");
}

// (() => {
// //  const a = "(assert (forall ((n4 Int) (recQs1835 Int)) (=> (and (X126 recQs1835 n4) (and (and (>= recQs1835 1) (>= recQs1835 (+ 1 (* (- 0 1) n4)))) (>= recQs1835 (+ 1 (* 1 n4))))) (X154 recQs1835 n4))))\n(assert (forall ((n4 Int)(n5 Int)) (+ 10 20)))(forall aaa bbb (+ 1 2))";
  
//  const a = require('fs').readFileSync('./src/model2.smt2', { encoding: 'utf-8'});
//  console.log(format(a));
// })();
