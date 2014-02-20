1: cancel. Bug. Find usages for Sorts don't display the sort definition among usages. Conversely, find usages
  for KLabels/functions display the definition location among usages. As for usages of names in a java program,
  definition is not displayed.

Status: While a consistent behaviour would be desired, I cannot find the cause of this problem. After a day of
  debugging I was unable to figure out why functions display their definition as usage, while sorts do not.
  Since this is a minor usability problem it is wise to cancel this bug and concentrate on other tasks.
  Intellij Idea is not without bugs and inconsistencies, and implementation code is virtually not documented.
  So it is better to be prepared for such situations and know when to stop.

2: ok. Bug: find usages in a file without "requires". If we search for a usage in such a file, usages will be searched
  in this file only. This is an optimization, to have faster search in K tutorial. In projects
  where there are multiple separate semantics, each in a single file. However this optimization don't work correctly
  for java module core.k.

So we need the following behaviour: if this file don't contain requires clauses but there are other
files in this project that have requires clauses pointing to this file, search for usages in the whole project.

3: cancel. In find usages view for K elements: functions, KLabels, Sorts, we want each occurrence to be displayed
  not just as a corresponding code line, but as a code line preceded by the name of the surrounding rule.

  Unfortunately it is unfeasible to implement this feature. The way lines are displayed is coded in the class chain:
    UsageInfo2UsageAdapter, UsageInfoToUsageConverter, FindUsagesManager. All class instantiation
      is hardcoded, and there is no way to replace one of the classes above with a custom class
      that would implement a different algorithm of displaying search lines. Thus the task cannot be completed.

4: Extending Ctrl+Q functionality. Visualising function/Label implementation as part of its documentation.
  When we hit Ctrl+Q on a function/label, we want the following to be displayed:

- a list of function syntax definitions, preceded by their documentation. The documentation for a module item
  is always the comment immediately preceding the item.
- a list of rules that implement the function, preceded by their documentation comment as well.
A rule is considered to implement the function if it either:
	- Contains the function name somewhere in its title. It doesn't have to start with the function name. If it is not
the title beginning, the preceding characters should not be "to" or "to-" - that is a sign that something is converted
to this function, e.g. a function call, not a function definition.
	- The rule have no name, but its body starts with the function name. This is a common pattern for short rules
for functions.
