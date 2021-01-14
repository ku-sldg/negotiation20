# negotiation20

Currently untargetted paper on negotiation of attestation protocols.
Assumes the `acmart` class is in the LaTeX load path.  The MacTeX 2019
automatically provides this.


## DepCoplandSub.v

This file includes the module `DepCopland`. In this module, there is a Privacy Policy that maps evidence to `True` or `False`. It is a fixpoint function and returns a `Prop` rather than a boolean. There is also a helper function `privPolicyT` defines the privacy policy over terms rather than evidence.  


This file also includes the module `IndexedCopland`. Here, terms are indexed by the type of evidence they produce. When a term is written, it is accompanied by a proof that it satisfies the PrivacyPolicy, `privPolicy`. This ensures each term is not exposing private information. 

## DepCoplandFn.v 

This file includes the module `DepCopland`. In this module, there is a fixpoint function for Privacy Policy, `privPolicy`, that maps evidence to `true` or `false`; the boolean values. There is also a function `privPolicyT` that allows the privacy policy to be defined over terms rather than evidence. The selection function is defined next, `selectDepFn`. This function takes a proof that the evidence satisfies the privacy policy before producing the evidence. It is a way to filter terms that do not satisfy the privacy policy. A `goodTerm` means that the term satisfies the privacy policy.  

## Discussion

### Subset Type and Index Type

There are two ways to weave together the subset type and the indexed type that should be considered:

1. Index `term` over evidence type and use the subset type predicate to determine `red`/`green` or go straight to `false`/`true`.  Something like `{x:(term e)|(privPolicy e)}`
2. Index `term` over `red`/`green` and check that status in the subset type predicate.  Something like `{x:(term c)|(fun c => c=green)}`. 

Are there others?

### Wiki

Do we want to leave this discussion in `README.md` or move it to the wiki area for the repo?