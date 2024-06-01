#!/bin/bash
# Time Travel Setup for Blind-Review Artifact Preparation
# Sets git commit timestamps to 2024-05-15 for anonymous artifact submission

export GIT_COMMITTER_DATE="2024-05-15 14:00:00"
export GIT_AUTHOR_DATE="2024-05-15 14:00:00"

echo "✓ Time travel configured:"
echo "  GIT_COMMITTER_DATE=$GIT_COMMITTER_DATE"
echo "  GIT_AUTHOR_DATE=$GIT_AUTHOR_DATE"
