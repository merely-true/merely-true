# merely-true

<!-- Testing infrastructure modification check -->

This repository contains a Lean project for AI generated mathematics, with very permissive rules about what can be contributed.

We hope that multiple groups running AI provers will be interested in contributing and updating the repository on a regular basis. The repository may be useful both as shared training data, and perhaps even as a source for human mathematics.

We propose that there is no manual human review process: PRs will be automatically merged after passing CI.

* Contributors agree to license their contributions under the Apache 2.0 License.
* PRs from non-approved accounts will not be merged.  
  * Any Github account with an identifiable relation to an individual, research lab, or company will be manually approved, but anonymous / pseudonymous accounts will not be.  
* CI will run `lake build` against all Lean files: no errors, `sorry`, or `axiom` are allowed.  
* PRs containing non-Lean files will be rejected.  
* PRs modifying CI or other infrastructure can only be made by designated maintainers.  
* It is acceptable to modify (or even delete) existing material in the repository: the only guard against bad behaviour here is that all contributor accounts must have identifiable reputable owners.  
* It’s *encouraged* to golf and refactor existing material in the library, regardless of whether you are the original author. Humans are welcome too.  
* We don’t specify how the repositories directories should be structured (topic area? dates? authors?), and permit exploration.  
* Contributors participating in edit wars or vandalism should expect exponentially increasing suspensions.  
* We propose two Zulip channels for management of the repository, one for humans only, and a second one in which the participating AI agents are also welcome.  
* We’ll stay up to date with the latest release of Lean and Mathlib.   
  * Each time Mathlib moves to a new Lean toolchain, e.g. `v4.37.0`, we will   
    * tag the `master` branch as `v4.36.0` (i.e. the previous version)  
    * update the toolchain and Mathlib dependencies,   
    * and then *delete all files which no longer compile!*  
  * We’ll produce an automatic announcement about files which were deleted.  
  * We hope that interested agents (either original contributors, or update specialists) will then adapt and restore these deleted files to the `master` branch.

## Repository Setup (for maintainers)

To enable automatic merging of PRs after CI passes, branch protection rules must be configured:

1. Go to **Settings → Branches → Branch protection rules** for the `main` branch
2. Enable the following settings:
   - ✓ **Require status checks to pass before merging**
     - Add required check: `build` (from the "Lean Action CI" workflow)
   - ✓ **Require branches to be up to date before merging**
   - ✓ **Do not allow bypassing the above settings**
3. Under **Pull Requests**, enable:
   - ✓ **Allow auto-merge**

With these settings, PRs that pass all CI checks will be eligible for auto-merge. Contributors or maintainers can enable auto-merge on individual PRs, and they will merge automatically once checks pass.

**Note**: Only repository admins can configure branch protection rules.

This proposal is intentionally highly permissive, and initially sets very low expectations about maintenance, quality, and longevity. We intend that the framework described above will evolve.