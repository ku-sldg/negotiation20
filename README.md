# negotiation20

Currently untargetted paper on negotiation of attestation protocols.
Assumes the `acmart` class is in the LaTeX load path.  The MacTeX 2019
automatically provides this.


## DepCoplandSub.v

This file includes the module `DepCopland`. In this module, there is a Privacy Policy that maps evidence to [True] or [False]. It is a fixpoint function and returns a `Prop` rather than a boolean. There is also a function `privPolicyT` defines the privacy policy over terms rather than evidence.  


This file also includes the module `IndexedCopland`. Here, terms are indexed by the type of evidence they produce. When a term is written, it is accompanied by a proof that it satisfies the PrivacyPolicy, `privPolicy`. This ensures each term is not exposing private information. 

## DepCoplandFn.v 

This file includes the module `DepCopland`. In this module, there is a fixpoint function for Privacy Policy, `privPolicy`, that maps evidence to [true] or [false]; the boolean values. There is also a function `privPolicyT` that allows the privacy policy to be defined over terms rather than evidence. The selection function is defined next, `selectDepFn`. This function takes a proof that the evidence satisfies the privacy policy before producing the evidence. It is a way to filter terms that do not satisfy the privacy policy. A `goodTerm` means that the term satisfies the privacy policy.  

