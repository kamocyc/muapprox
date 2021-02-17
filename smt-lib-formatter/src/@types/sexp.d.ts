// Type definitions for node_modules/sexp/index.js

declare namespace sexp {
  interface Options {
    translateSymbol?: (sym: string) => any;
    translateString?: (str: string) => any;
    translateNumber?: (str: string) => any; 
  }
}

declare function sexp(source : string, opts? : sexp.Options): any[];

export = sexp
