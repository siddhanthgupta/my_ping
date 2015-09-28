/*
 * my_ping.c
 *
 *  Created on: 20-Sep-2015
 *      Author: siddhanthgupta
 */
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>
#include <netdb.h>              // For protoent, gethostbyname
#include <limits.h>

#include <sys/errno.h>
#include <sys/types.h>
#include <sys/socket.h>         // For the sockets
#include <sys/time.h>           // For the gettimeofday() function

#include <arpa/inet.h>          // For inet_aton
#include <netinet/ip_icmp.h>    // For the ICMP header
#include <netinet/ip.h>

#define MAXPACKET   (65536 - 60 - 8)    // Max packet size
#define MAXIPLEN    60
#define MAXICMPLEN  76
#define MAXHOSTNAMELEN 1024
#define DEFDATALEN  (64 - 8)            // Default data length
#define MAXWAIT 10                      // Max time the ping program waits for a response
/*
 * MAX_DUP_CHK is the number of bits in received table, i.e. the maximum
 * number of received sequence numbers we can keep track of.  Change 128
 * to 8192 for complete accuracy...
 */
#define MAX_DUP_CHK (8 * 128)

int mx_dup_ck = MAX_DUP_CHK;
char rcvd_tbl[MAX_DUP_CHK / 8];

#define A(bit)      rcvd_tbl[(bit)>>3]      // Identify byte in an array
#define B(bit)      (1 << ((bit) & 0x07))   // Identify bit in byte
#define SET(bit)    (A(bit) |= B(bit))
#define CLR(bit)    (A(bit) &= (~B(bit)))
#define TST(bit)    (A(bit) & B(bit))

// Options Flags
int f_debug = 0;
int f_numeric = 0;
int f_pingfill = 0;
int f_quiet = 0;
int timing = 1;     // If size of packet < size of time struct, then we cannot
                    // send current time as part of the packet.

// Ping parameters
long int npackets = LONG_MAX;       // No of packets to send out
long int nreceived = 0;             // No of unique ECHO REPLY packets received
long int ntransmitted = 0;          // No of ECHO packets sent out
int interval = 1;                   // Interval (in seconds) after which echo is sent out
int ttl;                            // Time to live

// Ping statistics
long int tsum, tmin, tmax, nrepeats;

// Ping packet, socket and destination host details
int s;                              // Holds the socket file descriptor for the raw socket
int packlen;                        // Holds the length of the packet
u_char *packet;                     // Holds the transmitted/received packet
int ident;                          // Process ID to identify packets
struct sockaddr_in* destination;    // Holds the destination host details (address family, hostname, etc)
                                    // Defined in header netinet/in.h
int datalen = DEFDATALEN;           // Holds length of packet to be sent
char target[100];                   // Holds the destination host address (as input by the user)
char* hostname;                     // Holds the destination host name
struct sockaddr whereto;            // Holds the destination host details
struct hostent *hp;
char hnamebuf[MAXHOSTNAMELEN];

// Function definitions
void pinger();
void my_ping_usage(char** argv);
void finish();
void catcher();
int options();
static int in_cksum(u_short *addr, int len);
void pr_pack(char *received_packet, int cc, struct sockaddr_in *from);

/*
 * Creates the ICMP header (type ECHO REQUEST), and sends out the packet
 * to the destination host specified by the user
 */
void pinger() {
    struct icmphdr *icp;
    int cc;
    int i;

    // Creates the ICMP header
    // The OS auto-generates an IP packet to which this is attached
    u_char outpack[MAXPACKET];
    icp = (struct icmphdr *) outpack;
    icp->type = ICMP_ECHO;
    icp->code = 0;
    icp->checksum = 0;
    icp->un.echo.sequence = ++ntransmitted;
    icp->un.echo.id = ident;

    CLR(icp->un.echo.sequence % mx_dup_ck);

    // If packet round-trip times can be measured, then the current time
    // is sent out as the 8th byte of the ICMP header (bytes 0-7 form the ICMP header)
    if (timing)
        gettimeofday((struct timeval *) &outpack[8], (struct timezone *) NULL);

    // skips ICMP portion
    cc = datalen + 8;

    // Compute ICMP checksum here
    icp->checksum = in_cksum((u_short *) icp, cc);

    // Sends the ping packet to the destination
    i = sendto(s, (char *) outpack, cc, 0, &whereto, sizeof(struct sockaddr));
    if (i < 0 || i != cc) {
        if (i < 0) {
            fprintf(stderr, "FATAL ERROR: Unable to send out ping packets.\n");
            exit(2);
        }
        fprintf(stderr, "ping: wrote %s %d chars, ret=%d\n", hostname, cc, i);
    }
}

/*
 * in_cksum --
 *  Checksum routine for Internet Protocol family headers (C Version)
 *  Source is from FreeBSD open source code
 *
 *  Copyright (c) 1985, 1993
 *  The Regents of the University of California.  All rights reserved.
 *
 */
static int in_cksum(u_short *addr, int len) {
    register int nleft = len;
    register u_short *w = addr;
    register int sum = 0;
    u_short answer = 0;

    /*
     * Our algorithm is simple, using a 32 bit accumulator (sum), we add
     * sequential 16 bit words to it, and at the end, fold back all the
     * carry bits from the top 16 bits into the lower 16 bits.
     */
    while (nleft > 1) {
        sum += *w++;
        nleft -= 2;
    }

    /* mop up an odd byte, if necessary */
    if (nleft == 1) {
        *(u_char *) (&answer) = *(u_char *) w;
        sum += answer;
    }

    /* add back carry outs from top 16 bits to low 16 bits */
    sum = (sum >> 16) + (sum & 0xffff); /* add hi 16 to low 16 */
    sum += (sum >> 16); /* add carry */
    answer = ~sum; /* truncate to 16 bits */
    return (answer);
}

/*
 * Reads and processes the command line options, sets the socket options
 * and sets the destination address
 */
int options(int argc, char** argv) {
    int ch;
    // Processing command line options
    while ((ch = getopt(argc, argv, ":dc:i:n:qs:t:")) != EOF) {
        switch (ch) {
        case 'd':
            // Turns on the debug flag in the socket
            f_debug = 1;
            break;
        case 'c':
            // Number of packets to be sent
            npackets = atoi(optarg);
            if (npackets <= 0) {
                fprintf(stderr, "%s: bad number of packets to transmit.\n",
                        argv[0]);
                exit(2);
            }
            break;
        case 'i':
            // Interval between ping packets
            interval = atoi(optarg);
            if (interval <= 0) {
                fprintf(stderr, "%s: bad interval value.\n", argv[0]);
            }
            break;
        case 'n':
            // Numeric  output  only.
            // No attempt will be made to lookup symbolic names for host addresses.
            f_numeric = 1;
            break;
        case 'q':
            // Quiet output.  Nothing is displayed except the summary lines at  startup
            // time and when finished.
            f_quiet = 1;
            break;
        case 's':
            // Specifies the number of data bytes to be sent.
            datalen = atoi(optarg);
            if (datalen > MAXPACKET) {
                fprintf(stderr, "%s: packet size too large.\n", argv[0]);
                exit(2);
            }
            if (datalen <= 0) {
                fprintf(stderr, "%s: illegal packet size.\n", argv[0]);
                exit(2);
            }
            break;
        case 't':
            // Set the IP Time to Live.
            ttl = atoi(optarg);
            if (ttl < 0 || ttl > 255) {
                fprintf(stderr, "%s: ttl %d out of range.\n", argv[0], ttl);
                exit(2);
            }
            break;
        default:
            my_ping_usage(argv);
        }
    }
    // optind = index of next string after last processed argument
    argc -= optind;
    argv += optind;
    if (argc != 1)
        my_ping_usage(argv);
    strcpy(target, *argv);

    // If the timeval structure will fit within the specified packet
    // (default size = 56 bytes, and 8 bytes for ICMP header)
    if (datalen >= (int) sizeof(struct timeval))
        timing = 1;

    packlen = datalen + MAXIPLEN + MAXICMPLEN;
    packet = malloc((u_int) packlen);
    if (!packet) {
        fprintf(stderr, "ping: out of memory.\n");
        exit(2);
    }

    // ident holds the process id to identify our packets
    ident = getpid() & 0xFFFF;
    int hold = 1;

    // Set  the  SO_DEBUG  option  on the socket being used.  Essentially, this
    // socket option is not used by Linux kernel.
    if (f_debug) {
        setsockopt(s, SOL_SOCKET, SO_DEBUG, (char *) &hold, sizeof(hold));
    }

    // Setting destination address
    memset(&whereto, 0, sizeof(struct sockaddr));
    destination = (struct sockaddr_in *) &whereto;
    destination->sin_family = AF_INET;

    // If hostname is an IP address
    if (inet_aton(target, &destination->sin_addr)) {
        hostname = target;
    } else {
        // Hostname is not an IP address. We get host by its name
        hp = gethostbyname(target);
        if (!hp) {
            (void) fprintf(stderr, "ping: unknown host %s\n", target);
            exit(2);
        }
        destination->sin_family = hp->h_addrtype;
        if (hp->h_length > (int) sizeof(destination->sin_addr)) {
            hp->h_length = sizeof(destination->sin_addr);
        }
        memcpy(&destination->sin_addr, hp->h_addr, hp->h_length);
        (void) strncpy(hnamebuf, hp->h_name, sizeof(hnamebuf) - 1);
        hostname = hnamebuf;
    }
}

/*
 * Displays the correct usage for the program
 */
void my_ping_usage(char** argv) {
    fprintf(stderr,
            "usage: sudo %s [-dq] [-c count] [-i wait] [-p pattern] [-s packetsize] [-t ttl] host\n",
            argv[0]);
    exit(2);
}

/*
 * Displays the ping statistics and gracefully terminates the program
 */
void finish() {
    printf("--- %s ping statistics ---\n", hostname);
    printf("%ld packets transmitted, ", ntransmitted);
    printf("%ld packets received, ", nreceived);
    if (nrepeats)
        printf("+%ld duplicates, ", nrepeats);
    if (ntransmitted)
        if (nreceived > ntransmitted)
            printf("-- somebody's printing up packets!\n");
        else
            printf("%d%% packet loss\n",
                    (int) (((ntransmitted - nreceived) * 100) / ntransmitted));
    if (nreceived && timing)
        printf("round-trip min/avg/max = %ld.%ld/%lu.%ld/%ld.%ld ms\n",
                tmin / 10, tmin % 10, (tsum / (nreceived + nrepeats)) / 10,
                (tsum / (nreceived + nrepeats)) % 10, tmax / 10, tmax % 10);
    if (nreceived == 0)
        exit(1);
    exit(0);
}

/*
 * Displays the details of the packets received as ECHO REPLY
 */
void pr_pack(char *received_packet, int cc, struct sockaddr_in *from) {
    register struct icmphdr *icp;
    struct iphdr *ip;
    struct timeval tv, *tp;
    long triptime = 0;
    int hlen, dupflag;

    (void) gettimeofday(&tv, (struct timezone *) NULL);

    // Check the IP header
    ip = (struct iphdr *) received_packet;
    hlen = ip->ihl << 2;        // IHL * 4 bytes = size of header

    // Now the ICMP part
    cc -= hlen;
    icp = (struct icmphdr *) (received_packet + hlen);
    if (icp->type == ICMP_ECHOREPLY) {
        if (icp->un.echo.id != ident)
            return;
        ++nreceived;
        if (timing) {
            tp = (struct timeval *) (icp + 1);
            // Calculating round trip time by subtracting the time at which
            // packet was sent from the current value of time
            tv.tv_usec -= tp->tv_usec;
            if (tv.tv_usec < 0) {
                tv.tv_sec--;
                tv.tv_usec += 1000000;
            }
            tv.tv_sec -= tp->tv_sec;

            triptime = tv.tv_sec * 10000 + (tv.tv_usec / 100);
            tsum += triptime;
            if (triptime < tmin)
                tmin = triptime;
            if (triptime > tmax)
                tmax = triptime;
        }

        if (TST(icp->un.echo.sequence % mx_dup_ck)) {
            ++nrepeats;
            --nreceived;
            dupflag = 1;
        } else {
            SET(icp->un.echo.sequence % mx_dup_ck);
            dupflag = 0;
        }

        // If -q flag was specified, then the output only contains the finishing statistics
        // No packet information is printed
        if (f_quiet)
            return;

        // Displaying packet information
        printf("%d bytes from %s: icmp_seq=%u", cc,
                inet_ntoa(*(struct in_addr *) &from->sin_addr.s_addr),
                icp->un.echo.sequence);
        printf(" ttl=%d", ip->ttl);
        if (timing)
            printf(" time=%ld.%ld ms", triptime / 10, triptime % 10);
        if (dupflag)
            printf(" (DUP!)");
        printf("\n");
    }
}

/*
 * Causes a ping packet to be sent out every 1 second until the number of
 * ping packets sent out is < npackets
 *
 */
void catcher() {
    int waittime;
    // Sends out a ping
    pinger();
    // Sets catcher() function to handle the signal SIGALRM
    signal(SIGALRM, catcher);

    // Until number of packets delivered < npackets, generates
    // a SIGALRM signal every 1 second (interval set to 1 second by default)
    if (!npackets || ntransmitted < npackets)
        alarm((u_int) interval);
    else {
        // else sets a waittime = 2 * max round trip time or MAXWAIT, whichever is smaller
        if (nreceived) {
            waittime = 2 * tmax / 1000;
            if (!waittime)
                waittime = 1;
            if (waittime > MAXWAIT)
                waittime = MAXWAIT;
        } else
            waittime = MAXWAIT;

        // Sets the finish() function to handle the SIGALRM signal
        signal(SIGALRM, finish);
        // SIGALRM signals at the end of waittime and finish() is called
        alarm((u_int) waittime);
    }
}


/*
 * Main function : Sets up the socket, calls functions to read and process
 * command line arguments, starts the ping procedure, and receives any ECHO REPLY
 * packets received over the network
 */
int main(int argc, char** argv) {
    // Sets the protocol as ICMP
    struct protoent *proto = getprotobyname("icmp");

    // Making the socket (raw linux socket, ICMP protocol)
    // Note that making a raw socket required sudo privileges
    if ((s = socket(AF_INET, SOCK_RAW, proto->p_proto)) < 0) {
        if (errno == EPERM) {
            fprintf(stderr,
                    "%s: Root privileges required for opening socket.\n",
                    argv[0]);
            exit(1);
        }
        fprintf(stderr, "%s: Unable to open socket.\n", argv[0]);
        exit(1);
    }

    // Reading the command line options and processing them
    options(argc, argv);

    // SIGINT generated (Ctrl+c) will cause the finish() function to execute
    signal(SIGINT, finish);

    // Setting the catcher() function as handler for SIGALRM
    signal(SIGALRM, catcher);

    // If address family is IF_NET
    if (destination->sin_family == AF_INET)
        printf("PING %s (%s): %d data bytes\n", hostname,
                inet_ntoa(*(struct in_addr *) &destination->sin_addr.s_addr),
                datalen);
    else
        printf("PING %s: %d data bytes\n", hostname, datalen);

    // The catcher function sends out pings after fixed intervals
    catcher();

    // The do while loop receives the ICMP ECHO REPLY packets
    do {
        struct sockaddr_in from;
        register int cc;
        socklen_t fromlen;
        fromlen = sizeof(from);
        if ((cc = recvfrom(s, (char *) packet, packlen, 0,
                (struct sockaddr *) &from, &fromlen)) < 0) {
            fprintf(stderr,
                    "FATAL ERROR: Unable to receive ICMP ECHO REPLY packets");
        }
        // Processes the received packet and displays the relevant info
        pr_pack((char *) packet, cc, &from);
    }while (!(npackets && nreceived >= npackets));
    // The finish() function displays the statistics of the ping program
    finish();

    // Return with status = 0 (SUCCESS)
    return 0;
}
