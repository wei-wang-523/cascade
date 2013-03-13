int main(const unsigned char **pp, const unsigned char *eom) {
    unsigned int n;
    const unsigned char *cp, *init_cp, *last_cp;
    cp = *pp;
    init_cp = cp;
    last_cp = cp;
    if( cp < eom && (n = *cp++) != 0 ) {
        last_cp = cp;
    }
    return 0;
}
