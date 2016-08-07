extern void __VERIFIER_error() __attribute__ ((__noreturn__));

static void fail(void) {
ERROR: __VERIFIER_error();
}

struct slave_item {
    struct slave_item *next;
    struct slave_item *prev;
};
struct slave_item* alloc_or_die_slave(void)
{
    struct slave_item *ptr = malloc(sizeof(*ptr));
    if (!ptr)
        abort();
    ptr->next = ((void *)0);
    ptr->prev = ((void *)0);
    return ptr;
}
struct master_item {
    struct master_item *next;
    struct master_item *prev;
    struct slave_item *slave;
};
struct master_item* alloc_or_die_master(void)
{
    struct master_item *ptr = malloc(sizeof(*ptr));
    if (!ptr)
        abort();
    ptr->next = ((void *)0);
    ptr->prev = ((void *)0);
    ptr->slave = ((void *)0);
    return ptr;
}
void dll_insert_slave(struct slave_item **dll)
{
    struct slave_item *item = alloc_or_die_slave();
    struct slave_item *next = *dll;
    item->next = next;
    if (next)
        next->prev = item;
    *dll = item;
}
void* dll_create_generic(void (*insert_fnc)())
{
    void *dll = ((void *)0);
    insert_fnc(&dll);
    insert_fnc(&dll);
    while (__VERIFIER_nondet_int())
        insert_fnc(&dll);
    return dll;
}
struct slave_item* dll_create_slave(void)
{
    return dll_create_generic(dll_insert_slave);
}
void dll_destroy_slave(struct slave_item *dll)
{
    while (dll) {
        struct slave_item *next = dll->next;
        free(dll);
        dll = next;
    }
}
void dll_destroy_nested_lists(struct master_item *dll)
{
    while (dll) {
        dll_destroy_slave(dll->slave);
        dll = dll->next;
    }
}
void dll_reinit_nested_lists(struct master_item *dll)
{
    while (dll) {
        dll->slave = ((void *)0);
        dll = dll->next;
    }
}
void dll_destroy_master(struct master_item *dll)
{
    while (dll) {
        struct master_item *next = dll->next;
        free(dll);
        dll = next;
    }
}
void dll_insert_master(struct master_item **dll)
{
    struct master_item *item = alloc_or_die_master();
    struct master_item *next = *dll;
    item->next = next;
    if (next)
        next->prev = item;
    item->slave = dll_create_slave();
    *dll = item;
}
struct master_item* dll_create_master(void)
{
    return dll_create_generic(dll_insert_master);
}
void inspect_base(struct master_item *dll)
{
    do { if (!(dll)) fail(); } while (0);
    do { if (!(dll->next)) fail(); } while (0);
    do { if (!(!dll->prev)) fail(); } while (0);
    for (dll = dll->next; dll; dll = dll->next) {
        do { if (!(dll->prev)) fail(); } while (0);
        do { if (!(dll->prev->next)) fail(); } while (0);
        do { if (!(dll->prev->next == dll)) fail(); } while (0);
    }
}
void inspect_full(struct master_item *dll)
{
    inspect_base(dll);
    for (; dll; dll = dll->next) {
        struct slave_item *pos = dll->slave;
        do { if (!(pos)) fail(); } while (0);
        do { if (!(pos->next)) fail(); } while (0);
        do { if (!(!pos->prev)) fail(); } while (0);
        for (pos = pos->next; pos; pos = pos->next) {
            do { if (!(pos->prev)) fail(); } while (0);
            do { if (!(pos->prev->next)) fail(); } while (0);
            do { if (!(pos->prev->next == pos)) fail(); } while (0);
        }
    }
}
void inspect_dangling(struct master_item *dll)
{
    inspect_base(dll);
    for (; dll; dll = dll->next)
        do { if (!(dll->slave)) fail(); } while (0);
}
void inspect_init(struct master_item *dll)
{
    inspect_base(dll);
    for (; dll; dll = dll->next)
        do { if (!(!dll->slave)) fail(); } while (0);
}
int main()
{
    struct master_item *dll = dll_create_master();
    inspect_full(dll);
    dll_destroy_nested_lists(dll);
    inspect_dangling(dll);
    dll_reinit_nested_lists(dll);
    inspect_init(dll);
    dll_destroy_master(dll);
    return 0;
}
