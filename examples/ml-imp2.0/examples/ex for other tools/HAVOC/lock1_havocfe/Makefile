SRC = test_locks.c
OBJ = $(SRC:.c=.obj)

# the makefile uses INCLUDE env flag to search for windows headers (windows.h, stdio.h, etc.)
# run vcvars32.bat from C:\Program Files\Microsoft Visual Studio 8\VC\bin\vcvars32.bat to set INCLUDE from command prompt

# comment this line to compile without havoc
ANALYZE_OPT = /analyze:plugin $(HAVOC_INSTALL_DIR)\HavocFe.dll /analyze:log d.xml

all: $(OBJ)

.c.obj: 
	cl $(ANALYZE_OPT) -c -nologo $<

clean:
	del *.obj* d.xml*

