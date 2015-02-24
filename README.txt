
DESCRIPTION

  This folder contains the Coq development for
  Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning

  by
  
  Ralf Jung <jung@mpi-sws.org>
  David Swasey <swasey@mpi-sws.org>
  Filip Sieczkowski <filips@cs.au.dk>
  Kasper Svendsen <ksvendsen@cs.au.dk>
  Aaron Turon <turon@mpi-sws.org>
  Lars Birkedal <birkedal@cs.au.dk>
  Derek Dreyer <dreyer@mpi-sws.org>


CONTENTS

  Our artifact is a Coq formalization of the model of our Iris logic,
  together with a proof of adequacy (establishing that the model is
  faithful wrt the operational semantics) and a proof of soundness of
  the primitive rules of the logic wrt the model.

  NOTE: We have just mechanized the *soundness* of the *primitive*
  rules of Iris in Coq.  We have not mechanized the proofs of derived
  rules (i.e. those derivable from the primitive rules), nor have we
  mechanized the case study or other examples that are proven within
  the logic.  Proof outlines for the latter are given in the appendix
  that accompanied the POPL submission, and will be fleshed out even
  further for the final version of the appendix.

  The reason we focused on the primitive rules is that those are the
  rules whose soundness is proven by direct appeal to the semantic
  model of Iris.  For space reasons, we did not want to present the
  semantic model of Iris in any detail in the paper, but we still
  wanted to give the reader confidence in the results of the paper.
  With our Coq mechanization in hand, the reader can safely ignore the
  semantic model and instead focus on how to *use* the primitive rules
  of the logic (to derive more sophisticated rules or prove
  interesting examples).

  Mechanizing Iris proofs is a very interesting and important
  direction for future work, but it is beyond the scope of the paper.


  The folder is organized as follows:

  * core_lang.v contains the axioms about the language

  * lang.v defines the threadpool reduction and derives some lemmas
    from core_lang.v
  
  * masks.v introduces some lemmas about masks
  
  * world_prop.v uses the ModuRes Coq library to construct the domain
    for Iris propositions
  
  * iris_core.v defines world satisfaction and the simpler assertions
  
  * iris_vs.v defines view shifts and proves their rules
  
  * iris_wp.v defines weakest preconditions and proves the rules for
    Hoare triples
  
  * iris_meta.v proves adequacy, robust safety, and the lifting lemmas

  The development uses ModuRes, a Coq library by Sieczkowski et al. to
  solve the recursive domain equation (see the paper for a reference)
  and prove some of the standard separation logic rules. It is located
  in the lib/ subdirectory.


REQUIREMENTS

  Coq 

  We have tested the development using Coq 8.4pl4 on Linux and Mac
  machines. The entire compilation took less than an hour.
  

HOW TO COMPILE

  To compile the development, run
  
  > make -j

  in the folder containing this README. 
  


OVERVIEW OF LEMMAS

  Below we give a mapping from proof rules in the paper to Coq lemma's.

  RULE         Coq lemma
  -----------------------
  VSTimeless   iris_vs.v:/vsTimeless
  NewInv       iris_vs.v:/vsNewInv
  InvOpen      iris_vs.v:/vsOpen
  InvClose     iris_vs.v:/vsClose
  VSTrans      iris_vs.v:/vsTrans
  VSImp        iris_vs.v:/vsEnt
  VSFrame      iris_vs.v:/vsFrame
  FpUpd        iris_vs.v:/vsGhostUpd

  Ret          iris_wp.v:/htRet
  Bind         iris_wp.v:/htBind
  Frame        iris_wp.v:/htFrame
  AFrame       iris_wp.v:/htAFrame
  Csq          iris_wp.v:/htCons
  ACSQ         iris_wp.v:/htACons
  Fork         iris_wp.v:/htFork

  The main adequacy result is expressed by Theorem
  iris_wp.v:/adequacy_obs.

