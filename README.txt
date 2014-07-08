This folder contains the Coq development for Iris.
It uses a Coq library in lib/ by Sieczkowski et al. to solve the recursive domain equation (see the paper for a reference).

This folder is organized as follows:
* core_lang.v contains the axioms about the language
* lang.v defines the threadpool reduction and derives some lemmas from core_lang.v
* masks.v introduces some lemmas about masks
* world_prop.v uses the aforementioned Coq library to construct the domain for Iris propositions
* iris.v is the main file and contains the actual logic and the proof of the rules for view shifts and Hoare tiples

Run "make" in this folder to build it all.
Be aware that iris.v takes a long time to check and needs significant amounts of RAM!
8GiB may be sufficient, but to be safe you should have 16GiB and give it around 2 to 3 hours.
