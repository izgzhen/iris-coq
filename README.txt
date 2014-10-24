
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
  
  * iris.v is the main file and contains the actual logic and the
    proof of the rules for view shifts and Hoare triples

  The development uses ModuRes, a Coq library by Sieczkowski et al. to
  solve the recursive domain equation (see the paper for a reference)
  and prove some of the standard separation logic rules. It is located
  in the lib/ subdirectory.


REQUIREMENTS

  Coq 
  8GB ram + 4GB swap

  We have tested the development using Coq v. 8.4pl4 on Linux and Mac
  machines with at least 8GB RAM + 4GB swap.  The entire compilation
  took around 3 hours.
  

HOW TO COMPILE

  To compile the development, run
  
  > make 

  in the folder containing this README. 

  Be aware that iris.v takes a long time to check and needs
  significant amounts of RAM!
  


OVERVIEW OF LEMMAS

  Below we give a mapping from proof rules in the paper to Coq lemma's
  in Iris.v.

  RULE         Coq lemma
  -----------------------
  VSTimeless   vsTimeless
  NewInv       vsNewInv
  InvOpen      vsOpen
  InvClose     vsClose
  VSTrans      vsTrans
  VSImp        vsEnt
  VSFrame      vsFrame
  FpUpd        vsGhostUpd

  Ret          htRet
  Bind         htBind
  Frame        htFrame
  AFrame       htAFrame
  Csq          htCons
  ACSQ         htACons
  Fork         htFork

  The main adequacy result is expressed by Theorem soundness_obs.

