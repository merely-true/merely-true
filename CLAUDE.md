# Claude Instructions for merely-true

## Git workflow

Always create a new branch before committing changes. Never commit directly to `main`.
This allows contributions to be reviewed and merged via PRs per the repository's automated CI process.

```bash
git checkout -b <descriptive-branch-name>
# make changes
git add <files>
git commit -m "..."
gh pr create ...
```
