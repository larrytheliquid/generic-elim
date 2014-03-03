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

* [`GenericElim.DescL`](src/GenericElim/DescL.agda)

Notes
-----

The code is released under the [MIT licensed](code/LICENSE)