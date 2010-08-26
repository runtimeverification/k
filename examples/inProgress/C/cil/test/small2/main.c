
#pragma pack(1)

#pragma pack()

struct udf_sb_info
{
	struct buffer_head *s_block_bitmap[8 ];

	struct inode    *s_vat;
};

int main () {
 return 0;
}
