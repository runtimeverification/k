typedef enum {
        unused, mode, motion, report
} command_types;


// The attribute unused is shadowed by an enumeration

int * foo __attribute__ ((unused)) = 0;
