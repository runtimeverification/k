struct module
{
        unsigned long size_of_struct;
        const char *name;
};


static struct module kernel_module =
{
	size_of_struct:		sizeof(struct module),
	name: 			"",
};

int main () {
 return 0;
}
