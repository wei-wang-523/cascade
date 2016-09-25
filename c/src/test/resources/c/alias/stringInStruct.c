typedef unsigned int __u32;
typedef unsigned char __u8;
typedef __u8 uint8_t;
typedef __u32 uint32_t;

struct watchdog_info {
 __u32 options;
 __u32 firmware_version;
 __u8 identity[32];
};

static struct watchdog_info zf_info = {
 .options = 0x8000 | 0x0100,
 .firmware_version = 1,
 .identity = "ZF-Logic watchdog",
};


int main()
{
   return 0;
}