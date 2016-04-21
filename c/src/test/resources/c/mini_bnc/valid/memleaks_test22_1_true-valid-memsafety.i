typedef long unsigned int size_t;

struct ldv_list_head {
 struct ldv_list_head *next, *prev;
};

struct ldv_msg {
 void *data;
 struct ldv_list_head list;
};

struct ldv_device {
 void *platform_data;
 void *driver_data;
 struct ldv_device *parent;
};

struct ldv_usb_interface_descriptor {
 char bLength;
 char bDescriptorType;
 char bInterfaceNumber;
 char bAlternateSetting;
 char bNumEndpoints;
 char bInterfaceClass;
 char bInterfaceSubClass;
 char bInterfaceProtocol;
 char iInterface;
} __attribute__ ((packed));

struct ldv_usb_host_interface {
 struct ldv_usb_interface_descriptor desc;
};

struct ldv_usb_interface {
 struct ldv_usb_host_interface *altsetting;
 struct ldv_usb_host_interface *cur_altsetting;
 struct ldv_device dev;
};


typedef struct {
        int counter;
} ldv_atomic_t;

struct ldv_kref {
        ldv_atomic_t refcount;
};

struct ldv_kobject {
        char *name;
        struct ldv_list_head entry;
        struct ldv_kref kref;
};

static void ldv_kobject_release(struct ldv_kref *kref) {
 struct ldv_kobject *kobj = ({ const typeof( ((struct ldv_kobject *)0)->kref ) *__mptr = (kref); (struct ldv_kobject *)( (char *)__mptr - ((size_t) &((struct ldv_kobject *)0)->kref) );});
        char *name = kobj->name;
        free(kobj);


        if (name) {
                free(name);
        }
}

static inline int ldv_kref_sub(struct ldv_kref *_kref,
            void (*release)(struct ldv_kref *_kref))
{
        release(_kref);
        return 0;
}

void main(void) {
 struct ldv_kobject *_kobj;
 _kobj = malloc(sizeof(*_kobj));
 ldv_kref_sub(&_kobj->kref, ldv_kobject_release);
}
