/*
 *  Copyright (C) 2006-2012 Nigel Horne <njh@bandsman.co.uk>
 *
 *  This program is free software; you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation; either version 2 of the License, or
 *  (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *
 *  You should have received a copy of the GNU General Public License
 *  along with this program; if not, write to the Free Software
 *  Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 *  MA 02110-1301, USA.
 *
 * This program is a milter (i.e. a sendmail filter/plug-in) which blocks
 * connections from remote sites that are spamming us. The remote sites are
 * blocked for a configurable time.
 *
 * cc $CFLAGS blacklist-milter.c -lmilter -lpthread
 *	add -L/usr/lib/libmilter on Debian
 *
 * Before installing check the routine isWhiteList
 *
 * INPUT_MAIL_FILTER(`blacklist', `S=local:/var/run/blacklist, F=T, T=S:4m;R:4m')dnl
 * rm -f /var/run/blacklist
 * /usr/local/etc/blacklist local:/var/run/blacklist
 *
 * The latest development version is available
 *	from https://github.com/nigelhorne/blacklist-milter
 *
 * TODO: Rather than refuse connection, it may be better to state 'Unknown
 *	recipient' at the RCPT TO stage so that the spammer thinks the email
 *	isn't valid and may consider removing it (wishful thinking :-) )
 * TODO:	IPv6
 * TODO:	The location of the maillog should be configurable
 * TODO:	When stopping re-open firewall entries we've stopped
 *
 * Version 0.02: 27/1/07:
 *	Setuid to NOBODY
 *	Add and use pthread_sleep
 *	watchdog: fleshed out the syslogs
 * Version 0.03: 28/1/07:
 *	Note when a whitelist address has not been blocked
 *	TEMPFAIL when out of IDS
 *	Added whiteNets array
 * Version 0.04: 23/6/07:
 *	Include <errno.h>
 * Version 0.05: 24/9/07:
 *	Added support for sendmail 8.14 and confCONNECTION_RATE_THROTTLE
 * Version 0.06: 24/8/08:
 *	block 'too many open connections'
 *	correct the localNets structure
 * Version 0.07: 7/4/10
 *	Consolidate blacklist_cleanup and blacklist_abort
 *	Use the firewall to disallow connections
 * Version 0.08 7/5/12
 *	Added DEBUG mode
 *	Make sure don't put up firewall against whitelisted addresses
 *	Block those in SpamCop's black-list
 */
#include <stdio.h>
#include <sysexits.h>
#include <syslog.h>
#include <libmilter/mfapi.h>
#include <fcntl.h>
#include <unistd.h>
#include <string.h>
#include <stdlib.h>
#include <arpa/inet.h>
#include <errno.h>
#define __USE_GNU
#include <pthread.h>
#include <time.h>
#include <wait.h>

/*#define	DEBUG*/
#define	TIMEOUT	60
/*#define	TAIL_RESTART	120*60*/
/*#define	NOBODY	65534*/	/* Can't do this so that we can run iptables */

#define	MAIL_LOG	"/var/log/mail.log"

#define	uint32_t	unsigned long

#define PACKADDR(a, b, c, d) (((uint32_t)(a) << 24) | ((b) << 16) | ((c) << 8) | (d))
#define MAKEMASK(bits)	((uint32_t)(0xffffffff << (bits)))

static const struct cidr_net {
	uint32_t	base;
	uint32_t	mask;
} localNets[] = {
	/*{ PACKADDR(127,   0,   0,   0), MAKEMASK(8) },	/*   127.0.0.0/8 */
	{ PACKADDR(192, 168,   0,   0), MAKEMASK(16) },	/* 192.168.0.0/16 - RFC3330 */
	/*{ PACKADDR(192, 0,   2,   0), MAKEMASK(24) },	/* 192.0.2.0/24 - RFC3330 */
	{ PACKADDR( 10,   0,   0,   0), MAKEMASK(8) },	/*    10.0.0.0/8 */
	{ PACKADDR(172,  16,   0,   0), MAKEMASK(12) },	/*  172.16.0.0/12 */
	{ PACKADDR(169, 254,   0,   0), MAKEMASK(16) },	/* 169.254.0.0/16 */
	{ 0, 0 }
}, whiteNets[] = {
	{ PACKADDR(212, 159,   0,   0), MAKEMASK(19) },	/* F9 - 212.159.0.0/19 */
	{ PACKADDR(84,   93, 229,   0), MAKEMASK(8) }, /* F9 - 84.93.229.0/8 */
	{ PACKADDR(217,  157, 23, 243), MAKEMASK(0) },	/* njh.softcom.dk */
	{ PACKADDR(204,  15,  80,   0), MAKEMASK(22) },	/* Spamcop */
	{ 0, 0 }
};

struct	privdata {
	char	ip[INET_ADDRSTRLEN];	/* IP address of the other end */
};

/* map sendmailID to IP address */
#define	NIDS	100
static struct ip {	/* FIXME: mutex */
	char	ip[INET_ADDRSTRLEN];
	char	sendmailID[17];
	time_t	time;
	SMFICTX	*ctx;
} ips[NIDS];

#define	NBLACKLISTED	25
static struct bip {	/* FIXME: mutex */
	char	ip[INET_ADDRSTRLEN];
	time_t	time;
	const	char	*reason;
} bips[NBLACKLISTED];

static	sfsistat	blacklist_connect(SMFICTX *ctx, char *hostname, _SOCK_ADDR *hostaddr);
static	sfsistat	blacklist_header(SMFICTX *ctx, char *headerf, char *headerv);
static	sfsistat	blacklist_body(SMFICTX *ctx, u_char *bodyp, size_t len);
static	sfsistat	blacklist_cleanup(SMFICTX *ctx);
static	int	isLocalAddr(in_addr_t ip);
static	int	isWhiteList(const char *addr);
static	void	*watchdog(void *a);
static	void	tail(void);
static	char	*cli_strtok(const char *line, int fieldno, const char *delim);
static	void	timeout(void);
static	void	thread_sleep(int seconds);
static	int	rememberIP(SMFICTX *ctx, const char *addr);

int
main(int argc, char **argv)
{
	const char *port;
	pthread_t tid;
	struct smfiDesc smfilter = {
		"blacklist", /* filter name */
		SMFI_VERSION,	/* version code -- leave untouched */
		SMFIF_NONE,	/* flags - we only look */
		blacklist_connect, /* connection callback */
		NULL,		/* HELO filter callback */
		NULL,	/* envelope sender filter callback */
		NULL,	/* envelope recipient filter callback */
		blacklist_header, /* header filter callback */
		NULL,	/* end of header callback */
		blacklist_body,	/* body filter callback */
		NULL,	/* end of message callback */
		blacklist_cleanup,	/* message aborted callback */
		blacklist_cleanup,	/* connection cleanup callback */
#if	SMFI_VERSION > 2
		NULL,		/* Unrecognised command */
#endif
#if	SMFI_VERSION > 3
		NULL,		/* DATA command callback */
#endif
#if	SMFI_VERSION >= 0x01000000
		NULL,		/* Negotiation callback */
#endif
	};

	if(argc != 2) {
		fprintf(stderr, "Usage: %s socket-addr\n", argv[0]);
		return EX_USAGE;
	}

	openlog("blacklist-milter", LOG_CONS|LOG_PID, LOG_MAIL);

#ifndef	DEBUG
	switch(fork()) {
		case -1:
			perror("fork");
			return EX_OSERR;
		case 0:	/* child */
			break;
		default:	/* parent */
			return EX_OK;
	}
#endif

	port = argv[1];
	if(strncasecmp(port, "unix:", 5) == 0) {
		if(unlink(&port[5]) < 0)
			if(errno != ENOENT)
				perror(&port[5]);
	} else if(strncasecmp(port, "local:", 6) == 0) {
		if(unlink(&port[6]) < 0)
			if(errno != ENOENT)
				perror(&port[6]);
	} else if(port[0] == '/') {
		if(unlink(port) < 0)
			if(errno != ENOENT)
				perror(port);
	}
	/* sendmail->milter comms */
	if(smfi_setconn(port) == MI_FAILURE) {
		fprintf(stderr, "%s: smfi_setconn failed\n", argv[0]);
		return EX_SOFTWARE;
	}

	if(smfi_register(smfilter) == MI_FAILURE) {
		fprintf(stderr, "%s: smfi_register failed\n", argv[0]);
		return EX_UNAVAILABLE;
	}

	if(smfi_opensocket(1) == MI_FAILURE) {
		fprintf(stderr, "%s: can't open/create %s\n", argv[0], argv[1]);
		return EX_CONFIG;
	}

	syslog(LOG_INFO, "Starting blacklist");

#ifndef	DEBUG
	close(0);
	close(1);
	close(2);
	open("/dev/null", O_RDONLY);
	open("/dev/console", O_WRONLY);
	if(dup(1) < 0) {
		perror("dup");
		return EX_OSERR;
	}
#endif

	setpgrp();

	pthread_create(&tid, NULL, watchdog, NULL);

	return smfi_main();
}

/*
 * Sendmail wants to establish a connection to us
 */
static sfsistat
blacklist_connect(SMFICTX *ctx, char *hostname, _SOCK_ADDR *hostaddr)
{
	const char *remoteIP;
	struct privdata *privdata;
	time_t now;
	int i;
	struct bip *bip;
	char ip[INET_ADDRSTRLEN];	/* IPv4 only */

	if(hostname == NULL) {
		syslog(LOG_ERR, "blacklist_connect: hostname is null");
		return SMFIS_CONTINUE;
	}
	if((hostaddr == NULL) || (&(((struct sockaddr_in *)(hostaddr))->sin_addr) == NULL))
		/*
		 * According to the sendmail API hostaddr is NULL if
		 * "the type is not supported in the current version". What
		 * the documentation doesn't say is the type of what.
		 *
		 * Possibly the input is not a TCP/IP socket e.g. stdin?
		 */
		return SMFIS_ACCEPT;

	remoteIP = inet_ntop(AF_INET, &((struct sockaddr_in *)(hostaddr))->sin_addr, ip, sizeof(ip));

#ifdef	DEBUG
	printf("blacklist_milter: connection from %s\n", remoteIP);
#endif
	syslog(LOG_WARNING, "blacklist_milter: connection from %s", remoteIP);

	if(remoteIP == NULL) {
#ifdef	DEBUG
		puts("blacklist_connect: remoteIP is null");
#endif
		syslog(LOG_ERR, "blacklist_connect: remoteIP is null");
		return SMFIS_CONTINUE;
	}
	if(strcmp(remoteIP, "127.0.0.1") == 0) {
		/*syslog(LOG_DEBUG, "blacklist_connect: not scanning outgoing messages");*/
#ifdef	DEBUG
		puts("blacklist_connect: not scanning outgoing messages");
#endif
		return SMFIS_ACCEPT;
	}
	if(isLocalAddr(inet_addr(remoteIP))) {
#ifdef	DEBUG
		puts("blacklist_connect: not scanning local messages");
#endif
		/*syslog(LOG_DEBUG, "blacklist_connect: not scanning local messages");*/
		return SMFIS_ACCEPT;
	}
	if(isWhiteList(remoteIP)) {
		/*syslog(LOG_DEBUG, "blacklist_connect: not scanning %s", remoteIP);*/
#ifdef	DEBUG
		printf("blacklist_connect: not scanning %s\n", remoteIP);
#endif
		return SMFIS_ACCEPT;
	}
	for(i = 0, bip = bips; i < NBLACKLISTED; i++, bip++)
		if(strcmp(bip->ip, remoteIP) == 0) {
			now = time((time_t *)0);

			if((now - bip->time) < TIMEOUT) {
				syslog(LOG_NOTICE, "Rejected connexion from blacklisted IP %s for %s\n", remoteIP, bip->reason);
				thread_sleep(2);	/* waste their time */
				smfi_setreply(ctx, "550", "5.7.1", "Your IP is blacklisted because you are sending spam");
				bip->time = now;
				return SMFIS_REJECT;
			} else
				/* timeout */
				bip->ip[0] = '\0';
			break;
		}

	privdata = (struct privdata *)calloc(1, sizeof(struct privdata));
	smfi_setpriv(ctx, privdata);
	strcpy(privdata->ip, remoteIP);

	return SMFIS_CONTINUE;
}

static sfsistat
blacklist_header(SMFICTX *ctx, char *headerf, char *headerv)
{
	if(strcmp(headerf, "From") == 0) {
		if(strstr(headerv, "System Anti-Virus Administrator") ||
		   (strncasecmp(headerv, "mailsweeper@", 12) == 0) ||
		   strstr(headerv, "amavisd-new")) {
			smfi_setreply(ctx, "554", "5.7.1", "Forged bounce message not accepted - update your virus scanner");
			syslog(LOG_NOTICE, "Blocked by blacklist-milter");
			return SMFIS_REJECT;
		}
	} else if(strcmp(headerf, "Subject") == 0) {
		if((strcmp(headerv, "Virus in mail from you.") == 0) ||
		   (strcmp(headerv, "MailMarshal has detected a Virus in your message") == 0) ||
		   (strcmp(headerv, "Returned due to virus") == 0) ||
		   (strstr(headerv, "antivirus system report") != NULL) ||
		   (strcmp(headerv, "Aviso: Detectado formato de ficheiros invalido.") == 0) ||
		   (strcmp(headerv, "Warning: E-mail viruses detected") == 0) ||
		   (strcmp(headerv, "Banned file: message.scr in mail from you") == 0) ||
		   (strcmp(headerv, "Atención: Virus detectado en e-mail") == 0) ||
		   (strcmp(headerv, "Banned file: \"message_user.txt .pif\" in mail from you") == 0) ||
		   (strncmp(headerv, " Returned due to virus", 22) == 0) ||
		   (strncmp(headerv, "Virus Detected by ", 18) == 0) ||
		   (strcmp(headerv, "Virus Blocked") == 0) ||
		   (strcmp(headerv, "**Virus in mail from you**") == 0) ||
		   (strncmp(headerv, "[avast! - INFECTED]", 19) == 0) ||
		   (strstr(headerv, "ANTIVIRUS Notification") != NULL) ||
		   (strcmp(headerv, "VIRUS IN YOUR MAIL") == 0)) {
			smfi_setreply(ctx, "554", "5.7.1", "Forged bounce message not accepted - update your virus scanner");
			syslog(LOG_NOTICE, "Blocked by blacklist-milter");
			return SMFIS_REJECT;
		}
	}
	return SMFIS_CONTINUE;
}

static sfsistat
blacklist_body(SMFICTX *ctx, u_char *bodyp, size_t len)
{
	char *string = malloc(len + 1);
	int rc, i;
	struct privdata *privdata;
	time_t now;
	struct bip *bip;

	if(string == NULL)
		return SMFIS_CONTINUE;

	if(len == 0) {	/* unlikely */
		free(string);
		return SMFIS_CONTINUE;
	}

	memcpy(string, bodyp, len);
	string[len] = '\0';

	if(strstr(string, "One or more viruses were detected in the message") ||
	   strstr(string, "This message contains malware or a virus ") ||
	   strstr(string, "Virus Warning Message") ||
	   strstr(string, "infected with the W32/Netsky.p@MM virus and was not successfully cleaned.") ||
	   strstr(string, " contains virus W32.Email.W.NetSky.Q. Action: Deleted") ||
	   strstr(string, "Our firewall determined the e-mails containing worm copies are being sent from your computer.") ||
	   strstr(string, "The message has been blocked because it contains a component") ||
	   strstr(string, "virus(es) in your email to the following recipient(s):") ||
	   strstr(string, "An attachment in that mail was of a file type that the Spam Firewall is set to block.") ||
	   strstr(string, "Mail-Header, Mail-Body and Error Description are attached") ||
	   strstr(string, "The following email message was blocked by MailMarshal:") ||
	   strstr(string, "Il sistema antivirus ha rilevato una infezione nel messaggio:-") ||
	   strstr(string, "The original message content contained a virus or was blocked") ||
	   strstr(string, "Found virus WORM_MYDOOM.M in file ") ||
	   strstr(string, "Alerta! Posible Virus Detectado ") ||
	   strstr(string, "The following email message was blocked by ") ||
	   strstr(string, "Unrepairable Virus Detected. Your mail has not been sent.") ||
	   strstr(string, "ANTIVIRUS SYSTEM FOUND VIRUSES") ||
	   strstr(string, "An e-mail sent by you has been blocked by our automated software") ||
	   strstr(string, "Please check your system for viruses") ||
	   strstr(string, "foi rejeitado por conter virus") ||
	   strstr(string, "This is a message from the MailScanner E-Mail Virus Protection Service") ||
	   strstr(string, "was blocked by our Spam Firewall. The email you sent with the following subject ") ||
	   strstr(string, "Certain attachments are not allowed for security reasons.Your message has been rejected.")) {
		smfi_setreply(ctx, "554", "5.7.1", "Forged bounce message not accepted - update your virus scanner");
		syslog(LOG_NOTICE, "Blocked by blacklist-milter");
		rc = SMFIS_REJECT;
	} else
		rc = SMFIS_CONTINUE;

	free(string);
	privdata = smfi_getpriv(ctx);

	if(privdata == NULL)
		/*
		 * Not the first call to blacklist_body for this message
		 */
		return rc;

	now = time((time_t *)0);
	for(i = 0, bip = bips; i < NBLACKLISTED; i++, bip++)
		if(strcmp(bip->ip, privdata->ip) == 0) {
			if((now - bip->time) < TIMEOUT) {
				/*
				 * Another spam in the same connection
				 */
				syslog(LOG_NOTICE, "Rejected message from blacklisted IP %s\n", privdata->ip);
				smfi_setreply(ctx, "550", "5.7.1", "Your IP is blacklisted because you are sending spam");
				thread_sleep(2);	/* waste their time */
				bip->time = now;
				return SMFIS_REJECT;
			} else
				/* timeout */
				bip->ip[0] = '\0';
			break;
		}

	if(rememberIP(ctx, privdata->ip))
		return rc;

	free(privdata);
	smfi_setpriv(ctx, NULL);
	return SMFIS_TEMPFAIL;
}

static sfsistat
blacklist_cleanup(SMFICTX *ctx)
{
	struct privdata *p = smfi_getpriv(ctx);

	if(p) {
		int i;

		for(i = 0; i < NIDS; i++)
			if(ips[i].ctx == ctx) {
				ips[i].ip[0] = ips[i].sendmailID[0] = '\0';
				ips[i].ctx = NULL;
				break;
			}
		free(p);
		smfi_setpriv(ctx, NULL);
	}
	return SMFIS_CONTINUE;
}

static int
isLocalAddr(in_addr_t ip)
{
	const struct cidr_net *net;

	for(net = localNets; net->base; net++)
		if(htonl(net->base & net->mask) == (ip & htonl(net->mask)))
			return 1;

	return 0;	/* is non-local */
}

/*
 * Change this, and whiteNets as needed
 * FIXME: should be a runtime option
 */
static int
isWhiteList(const char *addr)
{
	const struct cidr_net *net;
	in_addr_t ip = inet_addr(addr);

	for(net = whiteNets; net->base; net++)
		if(htonl(net->base & net->mask) == (ip & htonl(net->mask)))
			return 1;

	if(strcmp(addr, "212.159.106.41") == 0)
		return 1;
	if(strcmp(addr, "212.159.3.225") == 0)
		return 1;
	if(strcmp(addr, "217.154.105.2") == 0)
		return 1;
	if(strcmp(addr, "204.15.82.124") == 0)
		return 1;
	if(strcmp(addr, "63.251.223.186") == 0)	/* CPAN */
		return 1;
	if(strncmp(addr, "205.15.8", 8) == 0)	/* SpamCop */
		return 1;

	return 0;
}

static void *
watchdog(void *a)
{
#ifdef	NOBODY
	tail();
	smfi_stop();
#else
	for(;;) {
		sleep(5);
		timeout();
		tail();
	}
#endif
	return NULL;
}

static void
tail(void)
{
	FILE *fin;
#if	defined(TAIL_RESTART) && (TAIL_RESTART > 0)
	time_t started = time((time_t *)0);
#endif
	char line[512];

	sprintf(line, "tail -F %s", MAIL_LOG);
	fin = popen(line, "r");

	if(fin == NULL) {
		perror(MAIL_LOG);
		syslog(LOG_ERR, "blacklist: can't start tail");
		return;
	}

#ifdef	NOBODY
	setuid(NOBODY);
#endif
	while(fgets(line, sizeof(line), fin)) {
		const char *sendmailID, *reason = NULL;
		char *ptr = NULL, *iaddr = NULL;
		int j;
		struct ip *ip;
		struct bip *bip;
		time_t now;

		/*
		 * Blacklist this sender's IP
		 */
		if(strstr(line, "Blocked by SpamAssassin") ||
		   strstr(line, "Blocked by blacklist-milter")) {
			ptr = cli_strtok(line, 3, ":");

			if(ptr) {
				int i;

				sendmailID = &ptr[1];

				for(i = 0, ip = ips; i < NIDS; i++, ip++)
					if(ip->sendmailID[0]) {
#ifdef	DEBUG
						printf("cmp '%s' '%s'\n", ip->sendmailID, sendmailID);
#endif
						if(strcmp(ip->sendmailID, sendmailID) == 0) {
							iaddr = ip->ip;
							reason = "sending spam";
							break;
						}
					}
				if(iaddr == NULL)
					syslog(LOG_WARNING, "Couldn't find sendmailID '%s' in the ips table", sendmailID);
			} else
				syslog(LOG_WARNING, "Couldn't parse the blocked line '%s'",
					line);
		} else if(strstr(line, "Connection rate limit exceeded") ||
			  strstr(line, "Too many open connections")) {
			ptr = cli_strtok(line, 3, "=");

			if(ptr) {
				sendmailID = NULL;

				if((iaddr = strchr(ptr, ',')) != NULL)
					*iaddr = '\0';
				iaddr = ptr;
				reason = "connecting too often";
			} else
				syslog(LOG_WARNING, "Couldn't parse the connection limit line '%s'",
					line);
		} else if(strstr(line, "Spam blocked see: http://spamcop.net/bl.shtml?")) {
			ptr = cli_strtok(line, 1, "?");

			if(ptr) {
				sendmailID = NULL;

				if((iaddr = strchr(ptr, '\n')) != NULL)
					*iaddr = '\0';
				iaddr = ptr;
				reason = "being in SpamCop's database";
			} else
				syslog(LOG_WARNING, "Couldn't parse the spamcop limit line '%s'",
					line);
		}

		if(ptr == NULL)
			continue;

		if(iaddr == NULL) {
			/*
			 * Usually this means that it's from a whitelisted IP,
			 * or we've just started up and this is from a
			 * connection which started before blacklist-milter
			 */
			if(sendmailID) {
#ifdef	DEBUG
				printf("%s: Couldn't determine the IP address\n",
					sendmailID);
#endif
				syslog(LOG_WARNING, "%s: Couldn't determine the IP address",
					sendmailID);
			} else {
				/* more serious */
#ifdef	DEBUG
				printf("Couldn't determine the IP address from '%s'\n", line);
#endif
				syslog(LOG_ERR, "Couldn't determine the IP address");
			}
			free(ptr);
			timeout();
			continue;
		}
		if(isWhiteList(iaddr))
			continue;
		now = time((time_t *)0);

#ifdef	DEBUG
		printf("Decided to block from '%s' because '%s'\n", line, reason);
#endif

		/*
		 * Determine if the IP address is already
		 * blacklisted
		 */
		for(j = 0, bip = bips; j < NBLACKLISTED; j++, bip++)
			if(strcmp(bip->ip, iaddr) == 0) {
#ifdef	DEBUG
				printf("%s is already blocked\n", iaddr);
#endif
				bip->time = now;
				break;
			}

		if(j == NBLACKLISTED)
			/*
			 * Not already blacklisted
			 */
			for(j = 0, bip = bips; j < NBLACKLISTED; j++, bip++)
				if(bip->ip[0] == '\0') {
#ifndef	NOBODY
					pid_t pid;
					int status;

					switch(pid = fork()) {
						case -1:
							perror("fork");
							break;
						case 0:
							if(execl("/sbin/iptables", "iptables", "-I", "INPUT", "-s", iaddr, "-j", "DROP", NULL) < 0) {
								perror("/sbin/iptables");
								_exit(errno);
							}
							/*NOTREACHED*/
					}
					if(sendmailID) {
#ifdef	DEBUG
						printf("%s: Will blacklist %s for %d seconds for %s\n",
							sendmailID, iaddr, TIMEOUT, reason);
#endif
						syslog(LOG_NOTICE, "%s: Will blacklist %s for %d seconds for %s",
							sendmailID, iaddr, TIMEOUT, reason);
					} else {
#ifdef	DEBUG
						printf("Will blacklist %s for %d seconds for %s\n",
							iaddr, TIMEOUT, reason);
#endif
						syslog(LOG_NOTICE, "Will blacklist %s for %d seconds for %s",
							iaddr, TIMEOUT, reason);
					}
					strcpy(bip->ip, iaddr);
					bip->time = now;
					bip->reason = reason;
					if(waitpid(pid, &status, 0) < 0)
						perror("wait");
					else if(WEXITSTATUS(status) == 0)
						syslog(LOG_NOTICE, "Kill host %s", iaddr);
					else
						fputs("iptables drop failed\n", stderr);
#else	/*!NOBODY*/
					strcpy(bip->ip, iaddr);
					bip->time = now;
					bip->reason = reason;
#endif	/*NOBODY*/
					break;
				}

		free(ptr);
		timeout();
#if	defined(TAIL_RESTART) && (TAIL_RESTART > 0)
		if((now - started) > TAIL_RESTART)
			break;
#endif
	}

#ifdef	NOBODY
	syslog(LOG_ERR, "blacklist: tail has died");
#else
	syslog(LOG_NOTICE, "blacklist: restarting tail");
#endif

	pclose(fin);
}

/* From clamAV */
static char *
cli_strtok(const char *line, int fieldno, const char *delim)
{
	int counter = 0, i, j;
	char *buffer;

	/* step to arg # <fieldno> */
	for(i = 0; line[i] && (counter != fieldno); i++)
		if(strchr(delim, line[i])) {
			counter++;
			while(line[i + 1] && strchr(delim, line[i + 1]))
				i++;
		}

	if(!line[i])
		/* end of buffer before field reached */
		return NULL;

	for(j = i; line[j]; j++)
		if(strchr(delim, line[j]))
			break;

	if(i == j)
		return NULL;

	buffer = malloc(j - i + 1);

	if(buffer == NULL)
		return NULL;

	strncpy(buffer, line + i, j - i);
	buffer[j - i] = '\0';

	return buffer;
}

static void
timeout(void)
{
	int i;
	time_t now = time((time_t *)0);
	struct ip *ip;
	struct bip *bip;

	for(i = 0, bip = bips; i < NBLACKLISTED; i++, bip++)
		if(bip->ip[0] && ((now - bip->time) > TIMEOUT)) {
#ifndef	NOBODY
			pid_t pid;
			int status;

			switch(pid = fork()) {
				case -1:
					perror("fork");
					return;
				case 0:
					/*close(0);
					close(1);
					close(2);
					open("/dev/null", O_RDONLY);
					open("/dev/null", O_WRONLY);
					dup(1);*/
					if(execl("/sbin/iptables", "iptables", "-D", "INPUT", "-s", bip->ip, "-j", "DROP", NULL) < 0) {
						perror("/sbin/iptables");
						_exit(errno);
					}
					/*NOTREACHED*/
			}
			if(waitpid(pid, &status, 0) < 0)
				perror("wait");
			else if(WEXITSTATUS(status) == 0) {
#ifdef	DEBUG
				printf("Accept host %s\n", bip->ip);
#endif
				syslog(LOG_NOTICE, "Accept host %s", bip->ip);
			} else
				fputs("iptables accept failed\n", stderr);
#endif	/*NOBODY*/
			bip->ip[0] = '\0';
		}

	for(i = 0, ip = ips; i < NIDS; i++, ip++)
		if(ip->ip[0] && ((now - ip->time) > TIMEOUT))
			ip->ip[0] = '\0';
}

static void
thread_sleep(int seconds)
{
	struct timeval tv;

	pthread_yield();

	tv.tv_sec = seconds;
	tv.tv_usec = 0;

	if(select(0, NULL, NULL, NULL, &tv) < 0)
		perror("select");
}

static int
rememberIP(SMFICTX *ctx, const char *addr)
{
	int i;
	time_t now = time((time_t *)0);
	struct ip *ip;

	for(i = 0, ip = ips; i < NIDS; i++, ip++)
		if((ip->ip[0] != '\0' && ((now - ip->time) < TIMEOUT)))
			if(ip->ctx == ctx) {
#ifdef	DEBUG
				printf("rememberIP %s->%s already known\n",
					ip->sendmailID, addr);
#endif
				return 1;
			}

#ifdef	DEBUG
	printf("rememberIP %s ID %s\n", addr, smfi_getsymval(ctx, "i"));
#endif

	for(i = 0, ip = ips; i < NIDS; i++, ip++)
		if((ip->ip[0] == '\0' || ((now - ip->time) > TIMEOUT))) {
			strcpy(ip->ip, addr);
			strcpy(ip->sendmailID, smfi_getsymval(ctx, "i"));
			ip->ctx = ctx;
#ifdef	DEBUG
			printf("rememberIP %s->%s\n", ip->sendmailID, addr);
#endif
			ip->time = now;
			break;
		}
	if(i == NIDS) {
		syslog(LOG_ERR, "blacklist_body: out of NIDS");

		timeout();
		return 0;
	}
	return 1;
}
