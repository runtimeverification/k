## Prerequisites

- Java 7
- Intellij Idea 12 with JFlex support plugin.
- Intellij Idea 13 with Grammar-Kit plugin.

## Building the plugin

- Open the project in Intellij Idea 13.
- Configure the plugin DevKit for the project.
- Open K.bnf
- Right click -> Generate Parser Code
- Open the same project in Intellij Idea 12.
- Configure the plugin DevKit.
- Go to Settings -> Compiler. Uncheck "Use external build".
- Build the project. Check that the file KLexer.java should be generated. If it is not, recheck the previous step.
- Close Idea 12. Idea 12 is only required to generate the lexer for the first time and whenever K.flex is changed.
- Reactivate Idea 13. If there is a warning suggesting to restart the project, ignore it.
- Build the project again. Should be successfully built.
- Build -> Prepare Plugin Module for deployment. This will create the jar file.

## References
- http://confluence.jetbrains.com/display/IntelliJIDEA/Custom+Language+Support
- http://habrahabr.ru/post/187106/ (try with google translate, some additional info compared to the first source)
- http://plugins.jetbrains.com/plugin/4230
