# Safe Checker

Implementation of a fuel-free, correct and complete type checker for PCUIC.
It is suited for extraction which would remove the termination and
correctness/completeness proofs.


| File                  | Description                                          |
|-----------------------|------------------------------------------------------|
| [PCUICWfReduction]    | Well-foundedness of the order used by the reduction machine
| [PCUICErrors]         | Output types used by the different machines
| [PCUICSafeReduce]     | Weak-head reduction machine
| [PCUICSafeConversion] | Conversion checker
| [PCUICWfEnv]          | Helper properties for global environments and universes
| [PCUICCallByNeed]     | Call-by-need conversion fast path that [PCUICTypeChecker] tries before the conversion checker
| [PCUICCallByNeedSound*] | Soundness of the fast path ([PCUICCallByNeedSoundHookProof.convert_cbn_sound])
| [PCUICTypeChecker]    | Type inference and type checking
| [PCUICSafeRetyping]   | Fast type inference, assuming well-typedness
| [PCUICSafeChecker]    | Checking of global environments
| [SafeTemplateChecker] | Checking of Template Rocq programs 
| [Extraction]          | Setup to extract the development
| [Loader]              | For plugins

[PCUICSafeReduce]: PCUICSafeReduce.v
[PCUICSafeConversion]: PCUICSafeConversion.v
[PCUICCallByNeed]: PCUICCallByNeed.v
[PCUICCallByNeedSound*]: PCUICCallByNeedSoundHookProof.v
[PCUICTypeChecker]: PCUICSafeChecker.v
[PCUICSafeRetyping]: PCUICSafeRetyping.v
[PCUICSafeChecker]: PCUICSafeChecker.v
[SafeTemplateChecker]: SafeTemplateChecker.v
[Loader]: Loader.v
[Extraction]: Extraction.v