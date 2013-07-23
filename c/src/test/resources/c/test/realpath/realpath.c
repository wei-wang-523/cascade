/****************************************************************************    
  Copyright (c) 1999,2000 WU-FTPD Development Group.  
  All rights reserved.
   
  Portions Copyright (c) 1980, 1985, 1988, 1989, 1990, 1991, 1993, 1994  
    The Regents of the University of California. 
  Portions Copyright (c) 1993, 1994 Washington University in Saint Louis.  
  Portions Copyright (c) 1996, 1998 Berkeley Software Design, Inc.  
  Portions Copyright (c) 1989 Massachusetts Institute of Technology.  
  Portions Copyright (c) 1998 Sendmail, Inc.  
  Portions Copyright (c) 1983, 1995, 1996, 1997 Eric P.  Allman.  
  Portions Copyright (c) 1997 by Stan Barber.  
  Portions Copyright (c) 1997 by Kent Landfield.  
  Portions Copyright (c) 1991, 1992, 1993, 1994, 1995, 1996, 1997  
    Free Software Foundation, Inc.    
   
  Use and distribution of this software and its source code are governed   
  by the terms and conditions of the WU-FTPD Software License ("LICENSE").  
   
  If you did not receive a copy of the license, it may be obtained online  
  at http://www.wu-ftpd.org/license.html.  
   
  $Id: realpath.c,v 1.2 2006/09/12 19:39:12 barrett Exp $  
   
****************************************************************************/
/* Originally taken from FreeBSD 3.0's libc; adapted to handle chroot
 * directories in BeroFTPD by Bernhard Rosenkraenzer
 * <bero@beroftpd.unix.eu.org>
 *
 * Added super-user permissions so we can determine the real pathname even
 * if the user cannot access the file. <lundberg+wuftpd@vr.net>
 */
/* config.h.  Generated automatically by configure.  */
/****************************************************************************

  Copyright (c) 1999,2000,2001 WU-FTPD Development Group.
  All rights reserved.

  Portions Copyright (c) 1980, 1985, 1988, 1989, 1990, 1991, 1993, 1994
    The Regents of the University of California.
  Portions Copyright (c) 1993, 1994 Washington University in Saint Louis.
  Portions Copyright (c) 1996, 1998 Berkeley Software Design, Inc.
  Portions Copyright (c) 1989 Massachusetts Institute of Technology.
  Portions Copyright (c) 1998 Sendmail, Inc.
  Portions Copyright (c) 1983, 1995, 1996, 1997 Eric P.  Allman.
  Portions Copyright (c) 1997 by Stan Barber.
  Portions Copyright (c) 1997 by Kent Landfield.
  Portions Copyright (c) 1991, 1992, 1993, 1994, 1995, 1996, 1997
    Free Software Foundation, Inc.

  Use and distribution of this software and its source code are governed
  by the terms and conditions of the WU-FTPD Software License ("LICENSE").

  If you did not receive a copy of the license, it may be obtained online
  at http://www.wu-ftpd.org/license.html.

  $Id: realpath.c,v 1.2 2006/09/12 19:39:12 barrett Exp $

****************************************************************************/

/*
 * Top level config file... These values will be adjusted by autoconf.
 * $Id: realpath.c,v 1.2 2006/09/12 19:39:12 barrett Exp $
 */

/*
 * allow "upload" keyword in ftpaccess
 */

#define UPLOAD 1

/*
 * allow "overwrite" keyword in ftpaccess.
 */

#define OVERWRITE 1

/*
 * allow "allow/deny" for individual users.
 */

#define HOST_ACCESS 1

/*
 * log failed login attempts
 */

#define LOG_FAILED 1

/*
 * log login attempts that fail because of class connection
 * limits.  Busy servers may want to prevent this logging
 * since it can fill up the log file and put a high load on
 * syslog.
 */
#define LOG_TOOMANY 1

/*
 * allow use of private file.  (for site group and site gpass)
 * NO_PRIVATE
 * Define this if you don't want to use the private authentication databases.
 */

/* #undef NO_PRIVATE */

/*
 * Try once more on failed DNS lookups (to allow far away connections
 * which might resolve slowly)
 */

#define	DNS_TRYAGAIN 1

/*
 * ANON_ONLY
 * Permit only anonymous logins... disables all other type
 * See FIXES-2.4-HOBBIT for more information on this option.
 */

/* #undef ANON_ONLY */

/*
 * PARANOID
 * Disable "questionable" functions
 * See FIXES-2.4-HOBBIT for more information on this option.
 */

/* #undef PARANOID */

/*
 * SKEY
 * Add SKEY support -- REQUIRES SKEY libraries
 * See FIXES-2.4-HOBBIT for more information on this option.
 */

/* #undef SKEY */

/*
 * OPIE
 * One-time Passwords In Everything (OPIE)
 * Add OPIE support -- REQUIRES OPIE libraries
 */

#if !defined (LINUX)		/* Linux autodetects OPIE */
/* #undef OPIE */
#endif

/*
 * ALTERNATE_CD
 * Causes "cd ~" to return the chroot-relative directory instead of the
 * real directory.
 */
#define ALTERNATE_CD 1

/*
 * UNRESTRICTED_CHMOD
 * If defined, any valid value for the mode will be accepted.
 * Otherwise, only values between 0 and 777 are accepted.
 */
/* #undef UNRESTRICTED_CHMOD */

/*
 * USE_RFC931
 * Define this if you want to use RFC 931 'authentication' - this improves
 * the logging at the cost of a possible slight delay in connection.
 */
/* #undef USE_RFC931 */

/*
 * BUFFER_SIZE
 * You can specify the buffer size for binary transfers; the defaults
 * are often far too small for efficiency.
 */
/* #undef BUFFER_SIZE */

/*
 * If you want to specify the syslog facility, you should modify CFLAGS in
 * the appropriate src/makefile/Makefile.*.
 */

/* If you want to set the paths where the configuration files, pids and logs
 * are stored, you should inspect src/pathnames.h and modify the appropriate
 * src/config/config.*.
 */

/*
 * RATIO
 * Support for Upload/Download ratios (may download x bytes for uploading 1 byte)
 */
/* #undef RATIO */

/*
 * OTHER_PASSWD
 * Support for using alternative passwd/shadow files
 */
/* #undef OTHER_PASSWD */

/*
 * DAEMON
 * If ftpd called with -D then run as a standalone daemon listing on the
 * ftp port.   This can speed up ftpd response as all ftpd then needs to
 * do is fork off a copy to handle an incoming request.  Under inetd
 * a new copy has to be opened and exec'd.
 */
#define DAEMON 1

/*
 * MAX_BACKLOG
 * Only used in DAEMON mode.
 * This is second parameter to listen.  It defines the number of incoming
 * processes to allow to backlog, prior to being accept() processing them,
 * before rejecting.
 */
#define MAX_BACKLOG 100

/*
 * MAPPING_CHDIR
 * Keep track of the path the user has chdir'd into and respond with
 * that to pwd commands.  This is to avoid having the absolue disk
 * path returned.  This helps avoid returning dirs like '.1/fred'
 * when lots of disks make up the ftp area.
 */

#define MAPPING_CHDIR 1

/*
 * THROUGHPUT
 * Keep track of total throughput for the user and limit if required.
 */

#define THROUGHPUT 1

/*
 * TRANSFER_COUNT
 * Keep track of total bytes for statistics.
 */

#define TRANSFER_COUNT 1

/*
 * TRANSFER_LIMIT
 * Limit file and bytes transferred in a session.
 */

#define TRANSFER_LIMIT 1

/*
 * NO_SUCKING_NEWLINES
 * Don't suppress some extra blank lines on messages and banners.
 */

/* #undef NO_SUCKING_NEWLINES */

/*
 * HELP_CRACKERS
 * Define this to help crackers break into your system by letting them
 * figure out which user names exist to guess passwords on.
 */

/* #undef HELP_CRACKERS */

/*
 * VERBOSE_ERROR_LOGING
 * Log all problems with USER and PASS as well as all rejected commands
 * and denied uploads/downloads.
 */

#define VERBOSE_ERROR_LOGING 1

/*
 * IGNORE_NOOP
 * Undefine this to let NOOP reset the idle timeout.
 */

#define IGNORE_NOOP 1

/*
 * XFERLOG_REALPATH
 * Define this to log the real path rather than the chroot-relative path for
 * files named in the xferlog.
 */

#define XFERLOG_REALPATH 1

/*
 * CLOSED_VIRTUAL_SERVER
 * Undefine this to allow real and non-owner guests to log in on a virutal server's address.
 */
#define CLOSED_VIRTUAL_SERVER 1

/*
 * NO_DNS
 * Define this to skip DNS lookups.  If the remote host name is needed, the
 * daemon uses the IP numbers instead.  'deny !nameserved' will always be
 * true (denying access) if this patch is enabled.
 *
 * This option is intended soley for very busy FTP sites where the added
 * security of DNS lookups is overshadowed by the speed and resource penalties.
 *
 * Disabling DNS lookups removes all protections against spoofing, making
 * remote user authentication virtually useless.  This option should only be
 * used on anonymous FTP servers.
 *
 * If you're not *absolutely sure* you need this, don't enable it.
 */
/* #undef NO_DNS */

/*
 * Some people don't like PASV and want to disable it.  Whatever.
 * PORT can be abused to attack other hosts.  Let's give the option to
 * disable one or the other.  We'll ignore DISABLE_PASV if you defined
 * DISABLE_PORT (hey, you gotta have at least one!).
 */
/* #undef DISABLE_PORT */
/* #undef DISABLE_PASV */

/*
 * Define this to suppress messages about PID locks causing the daemon to
 * sleep.  This should only be needed at busy sites.
 */
/* #undef NO_PID_SLEEP_MSGS */

/*
 * Define this to require the remove end of a PASV connection to have the
 * same IP as the control connection.  This limits, but does not eliminate,
 * the risk of PASV port race stealing the connection.  It also is non-RFC
 * compliant, so it may cause problems for some client sites.
 */
#define FIGHT_PASV_PORT_RACE 1

/*
 * Define this to completely disable anonymous FTP access.
 */
/* #undef NO_ANONYMOUS_ACCESS */

/*
 * Define this to have an ls command compiled into the daemon. That way you
 * don't need to put statically linked ls's into every chroot directory.
 */
/* #undef INTERNAL_LS */

/*
 * Define this if you want the internal ls to display UIDs/GIDs rather than
 * user/group names. This is faster, but doesn't look as nice.
 */
#define LS_NUMERIC_UIDS 1

/*
 * Define this if you want to hide setuid bits in the internal ls
 * this might be a good idea for security.
 */
#define HIDE_SETUID 1

/*
 * Undefine this if you don't want the enhanced DNS (resolver) features;
 * or if you cannot find libresolv on your system.
 */
#define HAVE_LIBRESOLV 1

/*
 * Define this if you want to support virtual servers
 */
#define VIRTUAL 1

/*
 * Define this if you want to be able to receive mail on anonymous
 * uploads
 */
#define MAIL_ADMIN 1

/*
 * Config files in /etc by default
 */
#define USE_ETC 1

/*
 * Define this to support quota mechanisms...
 */
/* #undef QUOTA */

/*
 * Define this to revert the NLST command to showing directories.
 *
 * This will cause mget to have errors when it attempts to RETR the
 * directory name (which is not a RETRievable object) but will revert
 * the NLST command enough to quell complains from Solaris command-
 * line FTP client users.
 */
/* #undef NLST_SHOWS_DIRS */

//#include <sys/param.h>
#include <sys/stat.h>

#include <errno.h>
//#if defined(HAVE_FCNTL_H)
//#include <fcntl.h>
//#endif
//#include <stdlib.h>
//#include <string.h>
//#include <unistd.h>

char *fb_realpath(const char *path, char *resolved);
char *getwd(char* c);

#ifndef MAXSYMLINKS		/* Workaround for Linux libc 4.x/5.x */
#define MAXSYMLINKS 5
#endif

#define HAVE_LSTAT 1

#ifndef HAVE_LSTAT
#define lstat stat
#endif

#define HAS_NO_FCHDIR 1
#define NULL	0  // Replace NULL as 0
/*
typedef struct {
  int max;
  int used;
  char *buf;
} cascade_string;
*/

#undef MAXPATHLEN
#define MAXPATHLEN 4

int strlen(const char *st) // size_t strlen
{
  int ret = 0;
  while (*st != '\0') {
    ++ret;
    ++st;
  }
  return ret;
}

char* strcpy(char * dest, const char *src) {
  char *ret;
  ret = dest;
  while(*src!='\0') {
    *dest = *src;
    dest++;
    src++;
  }
  *dest = *src;
  return ret;
}

char* strncpy(char *dest, const char *src, int n) { // size_t n
  int i = 0;
  char *ret;
  ret = dest;
  while(*src!='\0' && i<n) {
    *dest = *src;
    dest++;
    src++;
    i++;
  }
  while(i<n) {
    *dest = '\0';
    i++;
  }
  return ret;
}

char * strrchr(const char* s, int c) {
  char *found = '\0';
  while(*s!='\0') {
    if(*s==c) 
      found = (char*)s;
    s++;
  }
  return found;
}

char *strcat(char * dest, const char *src) {
  char *ret;
  ret = dest;
  while(*dest!='\0') {
    dest++;
  }
  while (*src!= '\0') {
    *dest = *src;
    dest++;
    src++;
  }
  *dest = *src;
  return ret;
}


char *wu_realpath(const char *path, char resolved_path[MAXPATHLEN], char *chroot_path)
{
  char *ptr;
  char q[MAXPATHLEN];

  fb_realpath(path, q);

  if (chroot_path == NULL)
    strcpy(resolved_path, q);
  else {
    strcpy(resolved_path, chroot_path);
    if (q[0] != '/') {
      if (strlen(resolved_path) + strlen(q) < MAXPATHLEN)
	strcat(resolved_path, q);
      else		/* Avoid buffer overruns... */
	return NULL;
    }
    else if (q[1] != '\0') {
      ptr = q;
      while (*ptr != '\0') ptr++;
      if (ptr == resolved_path || *--ptr != '/') {
	if (strlen(resolved_path) + strlen(q) < MAXPATHLEN)
	  strcat(resolved_path, q);
	else		/* Avoid buffer overruns... */
	  return NULL;
      }
      else {
	if (strlen(resolved_path) + strlen(q) - 1 < MAXPATHLEN)
	  strcat(resolved_path, &q[1]);
	else		/* Avoid buffer overruns... */
	  return NULL;
      }
    }
  }
  return resolved_path;
}

/*
 * char *fb_realpath(const char *path, char resolved_path[MAXPATHLEN]);
 *
 * Find the real name of path, by removing all ".", ".." and symlink
 * components.  Returns (resolved) on success, or (NULL) on failure,
 * in which case the path which caused trouble is left in (resolved).
 */

char *fb_realpath(const char *path, char *resolved)
{
  struct stat sb;
  
  int userid1, userid2, userid3, userid4, userid5, userid6, userid7, userid8; // uid_t
  int fd, n, rootd, serrno;
  int len; // size_t len
  char *tmp;
  char *p, *q, wbuf[MAXPATHLEN];
  int symlinks = 0;
  int resultcode;
  int err1_goto, err2_goto, loop_goto;
#ifdef HAS_NO_FCHDIR
  /* AIX Has no fchdir() so we hope the getcwd() call doesn't overrun the buffer! */
  char cwd[MAXPATHLEN + 1];
  char *pcwd;
#endif
  int errno_copy;
  /* Save the starting point. */
  errno_copy = 0;
  err1_goto = err2_goto = loop_goto = 0;
#ifdef HAS_NO_FCHDIR
#ifdef HAVE_GETCWD
  pcwd = getcwd(cwd, sizeof(cwd));
#else
  pcwd = getwd(cwd);
#endif
#else
  fd = open(".", O_RDONLY);
#endif
  if (EACCES == errno_copy) {
    userid1 = geteuid();
    delay_signaling();	/* we can't allow any signals while euid==0: kinch */
    seteuid(0);
#ifdef HAS_NO_FCHDIR
#ifdef HAVE_GETCWD
    pcwd = getcwd(cwd, sizeof(cwd));
#else
    pcwd = getwd(cwd);
#endif
#else
    fd = open(".", O_RDONLY);
#endif
    seteuid(userid1);
    enable_signaling();	/* we can allow signals once again: kinch */
  }
#ifdef HAS_NO_FCHDIR
  if (pcwd == NULL)
#else
    if (fd < 0)
#endif
      {
	(void) strcpy(resolved, ".");
	return (NULL);
      }

  /*
   * Find the dirname and basename from the path to be resolved.
   * Change directory to the dirname component.
   * lstat the basename part.
   *     if it is a symlink, read in the value and loop.
   *     if it is a directory, then change to that directory.
   * get the current directory name and append the basename.
   */
  (void) strncpy(resolved, path, MAXPATHLEN - 1);
  resolved[MAXPATHLEN - 1] = '\0';
  loop_goto = 1;
 loop:
  while(loop_goto==1) {
    err1_goto = err2_goto = loop_goto = 0;
    q = strrchr(resolved, '/');
    
    if (q != NULL) {
      p = q + 1;
      if (q == resolved)
	q = "/";
      else {
	do { // add do
	  --q;
	} while (q > resolved && *q == '/');
	q[1] = '\0';
	q = resolved;
      }
    
      errno_copy = 0;
      resultcode = chdir(q);
      if (EACCES == errno_copy) {
	userid2 = geteuid();
	delay_signaling();	/* we can't allow any signals while euid==0: kinch */
	seteuid(0);
	errno_copy = 0;
	resultcode = chdir(q);
	seteuid(userid2);
	enable_signaling();	/* we can allow signals once again: kinch */
      }
      if (resultcode < 0)
	err1_goto = 1;/* goto err1; */
    }
    else
      p = resolved;
    if(err1_goto!=1) {
      /* Deal with the last component. */
      if (*p != '\0') {
	errno_copy = 0;
	resultcode = lstat(p, &sb);
	if (EACCES == errno_copy) {
	  userid3 = geteuid();
	  delay_signaling();	/* we can't allow any signals while euid==0: kinch */
	  seteuid(0);
	  errno_copy = 0;
	  resultcode = lstat(p, &sb);
	  seteuid(userid3);
	  enable_signaling();	/* we can allow signals once again: kinch */
	}
	if (resultcode == 0) {
#ifdef HAVE_LSTAT
	  if (S_ISLNK(sb.st_mode)) {
	    if (++symlinks > MAXSYMLINKS) {
	      errno_copy = ELOOP;
	      err1_goto = 1;/*goto err1;*/
	    } else {
	      errno_copy = 0;
	      {
		len = strlen(p);
		tmp = calloc(len + 1, sizeof(char));
		if (tmp == 0) {
		  serrno = errno_copy;
		  err1_goto = 1;/*goto err1;*/
		} else {
		  strcpy(tmp, p);
		  p = tmp;
		}
	      }
	      if(err1_goto!=1) {
		n = readlink(p, resolved, MAXPATHLEN);
		if (EACCES == errno_copy) {
		  userid4 = geteuid();
		  delay_signaling();	/* we can't allow any signals while euid==0: kinch */
		  seteuid(0);
		  errno_copy = 0;
		  n = readlink(p, resolved, MAXPATHLEN);
		  seteuid(userid4);
		  enable_signaling();		/* we can allow signals once again: kinch */
		}
		if (n < 0) {
		  free(p);
		  err1_goto = 1;/*goto err1;*/
		} else {
		  free(p);
		  resolved[n] = '\0';
		  loop_goto = 1;/*goto loop;*/
		}
	      }
	    }
	  }
	  if(loop_goto!=1) {
	    if(err1_goto!=1) {
#endif /* HAVE_LSTAT */
	      if (S_ISDIR(sb.st_mode)) {
		errno_copy = 0;
		resultcode = chdir(p);
		if (EACCES == errno_copy) {
		  userid5 = geteuid();
		  delay_signaling();	/* we can't allow any signals while euid==0: kinch */
		  seteuid(0);
		  errno_copy = 0;
		  resultcode = chdir(p);
		  seteuid(userid5);
		  enable_signaling();		/* we can allow signals once again: kinch */
		}
		if (resultcode < 0)
		  err1_goto = 1;/*goto err1;*/
		else
		  p = "";
	      }
	    }
	  }
	}
      }
      if(loop_goto!=1) {
	if(err1_goto!=1) {
	  /*
	   * Save the last component name and get the full pathname of
	   * the current directory.
	   */
	  (void) strcpy(wbuf, p);
	  errno_copy = 0;
#ifdef HAVE_GETCWD
	  resultcode = getcwd(resolved, MAXPATHLEN) == NULL ? 0 : 1;
#else
	  resultcode = getwd(resolved) == NULL ? 0 : 1;
	  if (resolved[MAXPATHLEN - 1] != '\0') {
	    resultcode = 0;
	    errno_copy = ERANGE;
	  }
#endif
	  if (EACCES == errno_copy) {
	    userid6 = geteuid();
	    delay_signaling();	/* we can't allow any signals while euid==0: kinch */
	    seteuid(0);
	    errno_copy = 0;
#ifdef HAVE_GETCWD
	    resultcode = getcwd(resolved, MAXPATHLEN) == NULL ? 0 : 1;
#else
	    resultcode = getwd(resolved) == NULL ? 0 : 1;
	    if (resolved[MAXPATHLEN - 1] != '\0') {
	      resultcode = 0;
	      errno_copy = ERANGE;
	    }
#endif
	    seteuid(userid6);
	    enable_signaling();	/* we can allow signals once again: kinch */
	  }
	  if (resultcode == 0)
	    err1_goto = 1;/*goto err1;*/
	  else {
	    /*
	     * Join the two strings together, ensuring that the right thing
	     * happens if the last component is empty, or the dirname is root.
	     */
	    if (resolved[0] == '/' && resolved[1] == '\0')
	      rootd = 1;
	    else
	      rootd = 0;
	    /* (*wbuf && rootd==1) = false */
	    if (*wbuf) { 
	      if (strlen(resolved) + strlen(wbuf) + rootd + 1 > MAXPATHLEN) {
		errno_copy = ENAMETOOLONG;
		err1_goto = 1; /*goto err1;*/
	      } else {
		if (rootd == 1)
		  (void) strcat(resolved, "/");
		(void) strcat(resolved, wbuf);
	      
	      }
	    }
	    if(err1_goto!=1) {
	      /* Go back to where we came from. */
	      errno_copy = 0;
#ifdef HAS_NO_FCHDIR
	      resultcode = chdir(cwd);
#else
	      resultcode = fchdir(fd);
#endif
	      if (EACCES == errno_copy) {
		userid7 = geteuid();
		delay_signaling();	/* we can't allow any signals while euid==0: kinch */
		seteuid(0);
		errno_copy = 0;
#ifdef HAS_NO_FCHDIR
		resultcode = chdir(cwd);
#else
		resultcode = fchdir(fd);
#endif
		seteuid(userid7);
		enable_signaling();	/* we can allow signals once again: kinch */
	      }
	      if (resultcode < 0) {
		serrno = errno_copy;
		err2_goto = 1;/*goto err2;*/
	      } else {
	      
#ifndef HAS_NO_FCHDIR
		/* It's okay if the close fails, what's an fd more or less? */
		(void) close(fd);
#endif
		return (resolved);
	      }
	    }
	  }
	}
      }
    }
  }
 err1:
  if(err2_goto!=1) {
    serrno = errno_copy;
#ifdef HAS_NO_FCHDIR
    (void) chdir(cwd);
#else
    (void) fchdir(fd);
#endif
    if (EACCES == errno_copy) {
      userid8 = geteuid();
      delay_signaling();	/* we can't allow any signals while euid==0: kinch */
      seteuid(0);
#ifdef HAS_NO_FCHDIR
      (void) chdir(cwd);
#else
      (void) fchdir(fd);
#endif
      seteuid(userid8);
      enable_signaling();	/* we can allow signals once again: kinch */
    }
  }
#ifdef HAS_NO_FCHDIR
 err2:errno_copy = serrno;
#else
 err2:(void) close(fd);
  errno_copy = serrno;
#endif
  return (NULL);
}

int main() {
  char path[MAXPATHLEN];
  char resolved[MAXPATHLEN];

  char * ret = fb_realpath(path, resolved);

}
