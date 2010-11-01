#include <string.h>
struct dirent {
  char d_name[256];		 
};


typedef struct isc_direntry { 
  char 		name[256 ];
} isc_direntry_t;

typedef struct isc_dir {
  isc_direntry_t	entry;
} isc_dir_t;


void
isc_dir_init(isc_dir_t *dir) {

  dir->entry.name[0] = '\0';

}

unsigned int
isc_dir_read(isc_dir_t *dir) {
	struct dirent *entry;

	strcpy(dir->entry.name, entry->d_name);

	return (0);
}
