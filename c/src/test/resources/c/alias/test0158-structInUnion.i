int main()
{
	int a = 0;
	int b = 0;
    union {
        void *p0;
        struct {
            char c[2];
            void *p1;
            void *p2;
        } str;
    } data;
    data.p0 = &b;
    data.str.p2 = &a;
    free(data.p0);
    return 0;
}
