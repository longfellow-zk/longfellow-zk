This directory contains the files that define the Longfellow ZK spec.

## Setup
You will need the mmark and xml2rfc programs to work on this spec.
On mac, you can use `brew install mmark xml2rfc idnits`.

## Producing html
Running `make` produces the xml, text and html rendering.

## Updating the website
The [documentation workflow](../../.github/workflows/docs.yml) builds the spec and publishes the site from `main` when documentation changes.

## Issues
We intend to use the built-in issues system to manage edits and updates to this specification.
