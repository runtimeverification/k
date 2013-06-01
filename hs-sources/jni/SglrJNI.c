#include <jni.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include "sdf-wrapper.h"
#include "SglrJNI.h"
 
JNIEXPORT void JNICALL Java_SglrJNI_init(JNIEnv * a, jclass b) {
  init();
}

JNIEXPORT jbyteArray JNICALL Java_SglrJNI_parse
  (JNIEnv * env, jclass obj, 
   jstring pt, jstring prompt, jstring start, jstring input_file_name) {
     const jbyte *str_pt;
     const jbyte *str_prompt;
     const jbyte *str_start;
     const jbyte *str_input_file_name;
     str_pt = (const jbyte *)(*env)->GetStringUTFChars(env, pt, NULL);
     if (str_pt == NULL) {
         return NULL; /* OutOfMemoryError already thrown */
     }
     str_prompt =  (const jbyte *)(*env)->GetStringUTFChars(env, prompt, NULL);
     if (str_prompt == NULL) {
         return NULL; /* OutOfMemoryError already thrown */
     }
     str_start =  (const jbyte *)(*env)->GetStringUTFChars(env, start, NULL);
     if (str_start == NULL) {
         return NULL; /* OutOfMemoryError already thrown */
     }
     str_input_file_name =  (const jbyte *)(*env)->GetStringUTFChars(env, input_file_name, NULL);
     if (str_input_file_name == NULL) {
         return NULL; /* OutOfMemoryError already thrown */
     }
		int len=0;
     jbyte* buf = (jbyte *) parse((const char *)str_pt,(const char *)str_prompt,(const char *)str_start,(const char *)str_input_file_name, &len);
     (*env)->ReleaseStringUTFChars(env, pt, (char *) str_pt);     
     (*env)->ReleaseStringUTFChars(env, prompt, (char *) str_prompt);     
     (*env)->ReleaseStringUTFChars(env, start, (char *) str_start);     
     (*env)->ReleaseStringUTFChars(env, start, (char *) str_input_file_name);     
     jbyteArray ret = (*env)->NewByteArray(env, len);   
     (*env)->SetByteArrayRegion(env, ret, 0, len, buf);
     return ret;
}

