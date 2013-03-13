#include <sys/types.h>
#include <errno.h>

#define NS_CMPRSFLGS (0xc0)


/*
 * ns_name_skip(ptrptr, eom)
 *      Advance *ptrptr to skip over the compressed name it points at.
 * return:
 *      0 on success, -1 (with errno set) on failure.
 */
int
ns_name_skip(const u_char **ptrptr, const u_char *eom) {
        const u_char *cp;
        u_int n;

        /* BEGIN ANNOTE */
        const u_char *init_cp, *last_cp, *end_of_dn;
        /* END ANNOTE */

        cp = *ptrptr;
        /* BEGIN ANNOTE */
        init_cp = cp;
        last_cp = cp;
        /* END ANNOTE */

        /* LOOP INVARIANT: last_cp == cp && 
                           cp + sizeof(Dn(cp)) == init_cp + sizeof(Dn(init_cp)) */
        while (cp < eom && (n = *cp++) != 0) {
                /* Check for indirection. */
                switch (n & NS_CMPRSFLGS) {
                case 0:                 /* normal case, n == len */
                        /* ASSERT: is_label(Dn(last_cp)) */
                        cp += n;
                        /* ASSERT: rest(Dn(last_cp)) == Dn(cp) */
                        /* BEGIN ANNOTE */
                        last_cp = cp;
                        /* END ANNOTE */
                        continue;
                case NS_CMPRSFLGS:      /* indirection */
                        /* ASSERT: is_indirect(Dn(last_cp)) */
                        cp++;
                        /* BEGIN ANNOTE */
                        last_cp = cp;
                        /* END ANNOTE */
                        break;
                default:                /* illegal type */
                        __set_errno (EMSGSIZE);
                        return (-1);
                }
                break;
        }
        if (cp > eom) {
                __set_errno (EMSGSIZE);
                return (-1);
        }
        /* ASSERT: cp == init_cp + sizeof(Dn(init_cp)) */
        *ptrptr = cp;
        return (0);
}
