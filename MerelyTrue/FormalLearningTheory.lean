-- Formal Learning Theory Kernel
-- Machine-verified computational learning theory
-- Author: Dhruv Gupta (IISc Bangalore)
-- Repository: https://github.com/Zetetic-Dhruv/formal-learning-theory-kernel
--
-- 0 sorrys, 0 errors, verified by lean4checker --fresh
-- All theorems depend only on: propext, Classical.choice, Quot.sound
--
-- Key results:
--   fundamental_theorem: 5-way equivalence (PAC ↔ VCDim < ⊤ ↔ compression ↔ ...)
--   fundamental_vc_compression_with_info: Moran-Yehudayoff compression theorem
--   vc_characterization: PAC ↔ finite VC dimension
--   sauer_shelah: Sauer-Shelah-Perles lemma
--
-- NOTE: This code requires leanprover/lean4:v4.29.0-rc6 and matching Mathlib.
-- It will not compile against merely-true's current v4.24.0 toolchain.
-- See PR description for details.

import MerelyTrue.FormalLearningTheory.Basic
import MerelyTrue.FormalLearningTheory.Theorem.PAC
import MerelyTrue.FormalLearningTheory.Complexity.Compression
