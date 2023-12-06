# Mercury Cyber Object Exporter Plugin

** Copyright 2023, Mercury Cyber, LLC **

## Background

The Mercury Cyber object exporter is a derivation of the original publicly published XML Object Exporter
that was packaged with the Standard Services Build software.  It has been extensively modified to adapt
to customer needs and has been converted to a plugin, independent of the SailPoint Professional Services
plugin of the same functionality.

This plugin has had extensive new features added and is now available as part of our SailPoint Developer
site presence.  This documentation should suffice for most SailPoint Engineers.  Others may purchase support
at mercurycyber.com

The original changes made to the (non-plugin) version of the exporter were to:
- Converge the IIQ Deployment Accelerator generated files
- Create folders if they are not present
- XPath reverse tokenization
- Ability to add $date$ to folder name
- Ability to add $datetime$ to folder name

Newer changes:
- Can limit bundles additionally by type, hierarchy
- Can strip profiles from IT Roles (Bundles)
- Can strip RoleIndex and RoleScorecard from Bundle objects
- Can strip Email metadata from TaskDefinition
- A $NewDefault$ filename that keeps ALLCAPS words
- Re-addition of simple reverse tokenization option
- Improvements to merges
- Ignore file directory
- Include the hidden small class list option.
- Fixes to Description and Boolean tag issues
- Fixes to CDATA tag issues
- Addition of ZipFolder task to zip folders
