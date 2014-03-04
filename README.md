Generic Constructors and Eliminators from Descriptions
======================================================

Agda source code accompanying the draft paper (submitted for consideration to ICFP 2014):

[Generic Constructors and Eliminators from Descriptions - Dependently Typed Programming without the Algebra](http://bit.ly/1cxA0QF)

Code from the paper
-------------------

* Background Definitions
  * [Enumerations & Tags](src/GenericElim/Desc.agda#L12-L28)
  * [Descriptions](src/GenericElim/Desc.agda#L51-L75)
  * [Fixpoints](src/GenericElim/Desc.agda#L161-L192)
* Contributed Generic Definitions
  * [Un/CurriedBranches](src/GenericElim/Desc.agda#L30-L47)
  * [Un/CurriedEl](src/GenericElim/Desc.agda#L79-L102)
  * [Un/CurriedHyps](src/GenericElim/Desc.agda#L106-L157)
  * [Generic constructor inj](src/GenericElim/Desc.agda#L164-L165)
  * [Generic eliminator elim](src/GenericElim/Desc.agda#L196-L238)
* Examples
  * [Vector definitions](src/GenericElim/Desc.agda#L346-L427)
  * [Vector constructors using primitive init](src/GenericElim/Desc.agda#L429-L433)
  * [Vector constructors using derived inj](src/GenericElim/Desc.agda#L435-L439)
  * [Vector concat using primitive ind](src/GenericElim/Desc.agda#L443-L553)
  * [Vector concat using derived elim](src/GenericElim/Desc.agda#L557-L579)
* Correctness
  * [Soundness](src/GenericElim/Desc.agda#L242-L254)
  * [Completeness](src/GenericElim/Desc.agda#L256-L342)

Stratified version of code using universe levels
------------------------------------------------

* Background Definitions
  * [Enumerations & Tags](src/GenericElim/DescL.agda#L12-L28)
  * [Descriptions](src/GenericElim/DescL.agda#L51-L75)
  * [Fixpoints](src/GenericElim/DescL.agda#L161-L192)
* Contributed Generic Definitions
  * [Un/CurriedBranches](src/GenericElim/DescL.agda#L30-L47)
  * [Un/CurriedEl](src/GenericElim/DescL.agda#L79-L102)
  * [Un/CurriedHyps](src/GenericElim/DescL.agda#L106-L157)
  * [Generic constructor inj](src/GenericElim/DescL.agda#L164-L165)
  * [Generic eliminator elim](src/GenericElim/DescL.agda#L196-L238)
* Examples
  * [Vector definitions](src/GenericElim/DescL.agda#L346-L427)
  * [Vector constructors using primitive init](src/GenericElim/DescL.agda#L429-L433)
  * [Vector constructors using derived inj](src/GenericElim/DescL.agda#L435-L439)
  * [Vector concat using primitive ind](src/GenericElim/DescL.agda#L443-L553)
  * [Vector concat using derived elim](src/GenericElim/DescL.agda#L557-L579)
* Correctness
  * [Soundness](src/GenericElim/DescL.agda#L242-L254)
  * [Completeness](src/GenericElim/DescL.agda#L256-L342)

Comparing Definition using `ind` vs `elim`
------------------------------------------

In the paper we broke up the definition of `concat` using `ind` into
pieces because it was so big, and showed the definition using `elim`
inlined. Here is the definition of a similar function, `append`, using
`ind` and `elim` where both definitions are inlined:

* [append using ind](src/GenericElim/Desc.agda#L477-L497)
* [append using elim](src/GenericElim/Desc.agda#L571-L574)

Notes
-----

The code is released under an [MIT license](src/LICENSE)