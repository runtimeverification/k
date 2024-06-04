# K-REPL Client

This package contains a CLI client for the server that implements the K-REPL
commands. The commands are implemented via calls to the server API.

The commands below provide a CLI interface to the API that is suitable for
interactive debugging. Slightly different interfaces may be exposed in a
graphical or web client later on. 

Below are a list of commands supported by the K-REPL CLI along with
their expected parameters and output.

## Initialization

### load

#### Params

All parameters are optional, but some may in fact be required by some
semantics.

* program: String. A file path pointing to the program to parse and initialize
as the initial configuration. By default, parses as if `krun program` was
run.
* module: String. An optional K module to use to parse the program with.
* sort: String. An optional K sort to parse the program as.
* params: {String: (String, String, String)}. An optional map from parameter
name to (program, module, sort) tuples corresponding to the configuration
parameters of the semantics. Providing the empty string for any module or sort
name corresponds to the default parser for that parameter if one exists.

#### Behavior

Parses the provided program and initializes the REPL with the resulting initial
configuration.

### load-raw

#### Params

* program: String. A file path pointing to a kore configuration to use as the
initial configuration.

#### Behavior

Initializes the REPL with the specified initial configuration.

## Stepping

### step

#### Params

* depth: Int. Default 1. The number of rewrite steps to take.

#### Asynchronous Behavior

Generates new configuration(s) if they does not yet exist taken by stepping the
current configuration `depth` steps.

#### Returns

An asynchronous request identifier.

### rewind

#### Params

* depth: Int. Default 1. The number of rewrite steps to go back.

#### Asynchronous Behavior

Generates a new configuration if it does not yet exist taken by rewinding the
current configuration `depth` steps.

#### Returns

An asynchronous request identifier.

### step-to-branch

#### Asynchronous Behavior

Generates a new configuration if it does not yet exist taken by stepping the
current configuration until just prior to the next configuration branching
event.

#### Returns

An asynchronous request identifier.

### wait-for

#### Params

* requestId: Int

#### Behavior

Returns only after the specified asynchronous request has completed.

#### Returns

* The return value of the asynchronous command if one exists.

### check-completion

#### Params

* requestId: Int

#### Returns

* NotDone if the command is not complete, otherwise the return value of the
command.

## Printing Configurations

### show

#### Params

* id: ConfigId. Defaults to current configuration. The name of the
configuration to show.

#### Returns

The configuration, pretty-printed.

### show-diff

#### Params

* from: ConfigId. Defaults to last-printed configuration.
* to: ConfigId. Defaults to current configuration.

#### Returns

A diff between the two specified configurations.

### show-cell

#### Params:

* cells: List[String]. A list of cells to print. The empty list prints the k
cell.

#### Returns

A list of strings containing each pretty printed cell.

### show-cfg

#### Params

* dot: Bool.

#### Returns

The control flow graph. Textual if `dot` is false, otherwise as a `dot` file.

## ConfigId management

### alias

#### Params

* id: ConfigId. The configuration to give a name to.
* name: String. The name that becomes a new ConfigId.

#### Behavior

Assigns the specified configuration a new alias with the specified name.

### list-aliases

#### Params

* id: ConfigId. The configuration to list aliases for.

#### Returns

The list of aliases for the specified configuration.

### rm-alias

#### Params

* id: ConfigId. The alias to remove.

#### Behavior

Deletes the specified alias.

## State management

### select

#### Params

* id: ConfigId. Required.

#### Behavior

Sets the current configuration to the specified one.

### predecessor

#### Params

* id: ConfigId. Defaults to current configuration.

#### Returns

The predecessor of the specified configuration.

### successors

#### Params

* id: ConfigId. Defaults to current configuration.

#### Returns

The successors of the specified configuration.

### edit

#### Params

* id: ConfigId. Defaults to current configuration.
* cell: String. Name of cell to edit.
* value: String. Value to place in that cell.
* sort: String. Optional sort to use for parsing.
* module: String. Optional module name to use for parsing.

#### Behavior

Edits the specified cell of the specified configuration, replacing its current
contents with the specified value, and creating a new state for that edited
configuration if it does not yet exist. By default, uses the sort of the cell
and the main module.

### case-split

#### Params

* id: ConfigId. Defaults to current configuration.
* condition: String. Value to parse as a boolean condition. Defaults to parsing using main module of definition.
* module: String. Optional module name to use for parsing.

#### Behavior

Parses the specified condition as a term of sort `Bool` and creates two new nodes in the graph, one with `\equals(condition, true)`
and one with `\equals(condition, false)`. Each one consists of the relevant condition conjuncted with the specified configuration.
