
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
  faithful wrt the operational semantics), and a proof of soundness of
  the primitive rules of the logic wrt the model.


  The folder is organized as follows:

  * core_lang.v contains the axioms about the language

  * lang.v defines the threadpool reduction and derives some lemmas
    from core_lang.v
  
  * masks.v introduces some lemmas about masks
  
  * world_prop.v uses the aforementioned Coq library to construct the
    domain for Iris propositions
  
  * iris.v is the main file and contains the actual logic and the
    proof of the rules for view shifts and Hoare triples

  It uses a Coq library in lib/ by Sieczkowski et al. to solve the
  recursive domain equation (see the paper for a reference).


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
  VSOpen       vsOpen
  VSClose      vsClose
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
