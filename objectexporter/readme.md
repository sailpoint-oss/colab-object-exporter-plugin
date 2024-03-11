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

Version 1.0.2 Changes:
- Fixed issue with ignore functionality on Workgroups
- The class type of a Workgroup is actually Identity so in order match up the
- classes on an ignore operation, the workgroup attribute is checked and the
- name of the class is artifically changed to Workgroup.

Version 1.0.3 Changes:
- A bug was discovered where some of the functions, such as remove environmental
- attributes, was actually modifying the actual objects and saving them back to
- the environment.  To fix this I modified the code to operate on a deepCopy of
- every instance it worked on.
- Also if you want to remove the Task email but tokenize the task host, you
- couldn't do that.  So now if you check the box to remove the environment
- attributes, you should reverse tokenize the host value.  An example will be:

/TaskDefinition[@name\='XYZ\ Export\ Application']/Attributes/Map/entry[@key\='TaskSchedule.host']/@value=%%EXPORT_TASK_SERVER%%

Version 1.0.4 Changes:
- Enhancement: IdentityTrigger objects which are not disabled cannot have their
- disabled flag reverse tokenized because the attribute does not exist in the
- XML.  It needed to be added.  We might also need to add this to other objects.

Example:
/IdentityTrigger[@name\='RapidSetup\ Joiner']/@disabled=%%RS_TRIGGER_DISABLED%%
/IdentityTrigger[@name\='RapidSetup\ Mover']/@disabled=%%RS_TRIGGER_DISABLED%%
/IdentityTrigger[@name\='RapidSetup\ Leaver']/@disabled=%%RS_TRIGGER_DISABLED%%

- The code finds the first disabled=, name=, and type= tags in the XML and if
- the disabled= is not found OR is after the name= tag, then a disabled="false"
- is inserted before the name= tag and the full XML with those changes is sent
- to the reverse tokenization engine.
- The object of this reverse tokenization is to allow an initial production
- build to be deployed from the SSB with all of the IdentityTrigger objects
- disabled.  The example %%RS_TRIGGER_DISABLED%% would be false for the lower
- tier environments and true for prod.target.properties file.
