open Ast
open Ast.Logic

module type SynthesizerType = sig
  (* 
     EXPI : information for template/decisiontree/geometric synthesizers        
     EXPICS : information for particle bp/bp synthesizer
   *)
  type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list
                           * Constraint.t list
  type ty_ex_info = TyEXPICS
  val ty_ex_info: ty_ex_info
  val mk_candidates: ex_info ->
          ExampleInstance.t -> (((Ident.pvar * ((Ident.tvar * Sort.t) list)) * Formula.t) list) list
end

module TBSynthesizer : SynthesizerType = TBSynthesizer
  
module SCQMSynthesizer : SynthesizerType = SCQMSynthesizer
  
module DTSynthesizer : SynthesizerType = DTSynthesizer
  
module LTBSynthesizer : SynthesizerType = LTBSynthesizer

module PASPSynthesizer : SynthesizerType = PASIDSynthesizer

module PASATSynthesizer : SynthesizerType = PASATSynthesizer

module Union (Left: SynthesizerType) (Right: SynthesizerType) : SynthesizerType =
  struct
    type ex_info = EXPICS of (Ident.pvar * Sort.t list * bool) list * Constraint.t list
    type ty_ex_info = TyEXPICS

    let ty_ex_info = TyEXPICS
    let mk_candidates ex_info sample = 
      match ex_info with
      | EXPICS (infos, constraints) ->
         let left_res = try 
             Left.mk_candidates (Left.EXPICS (infos, constraints)) sample
           with _ -> [] in
         let right_res = try
             Right.mk_candidates (Right.EXPICS (infos, constraints)) sample 
           with _ -> [] in
         left_res @ right_res
  end

module TB_DT_Synthesizer : SynthesizerType = Union(TBSynthesizer)(DTSynthesizer)

module TB_DT_PASATSynthesizer : SynthesizerType = Union(TB_DT_Synthesizer)(PASATSynthesizer)
