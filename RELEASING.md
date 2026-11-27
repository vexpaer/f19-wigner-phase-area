# Archival release checklist

1. Confirm the manuscript, abstract, citation metadata and README match the actual theorem scope. Disclose AI assistance and distinguish formalized mathematical statements from physical interpretation.
2. Build the Lean project with the pinned toolchain and Mathlib release:
   `lake update && lake exe cache get && lake build && lake env lean F19/Algebra.lean`.
   Check the axiom report and the GitHub Actions result for the exact source to be released.
3. Build the PDF from the current manuscript:
   ```sh
   cd paper
   pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
   pdflatex -interaction=nonstopmode -halt-on-error manuscript.tex
   ```
   Inspect the PDF and commit `paper/manuscript.pdf` before tagging. The PDF must be in the tagged repository tree, not only in the release attachments.
4. Enable this repository in Zenodo's GitHub integration before publishing a new release. The existing GitHub tag v0.1.0 predates these archival metadata files. Suggested next archival tag: v1.0.0. Do not move or overwrite existing tags.
5. Publish the new GitHub release from the verified commit, then confirm the Zenodo record, metadata, downloadable archive and DOI. Add the DOI to README and citation metadata after it exists. Future releases should use distinct version tags.
6. Never describe a restricted-sector proof as a complete solution to F19. Include the precise Lean coverage and independent-review status in each release note.

No DOI is assigned by this repository configuration alone.
