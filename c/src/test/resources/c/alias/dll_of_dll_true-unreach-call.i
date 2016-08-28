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

int main()
{
    struct master_item *dll = dll_create_master();
    return 0;
}
