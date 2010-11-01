typedef void *PVOID;

typedef struct _CALLBACK_OBJECT *PCALLBACK_OBJECT;


__declspec(dllimport)
int
ExCreateCallback (
     PCALLBACK_OBJECT *CallbackObject,
     int ObjectAttributes,
     int Create,
     int AllowMultipleCallbacks
    );

