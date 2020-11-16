/////////////////////////////////////////////////////
//
// EpsLin Neo v1.56
// based on EpsLin (c) Juha Forsten 5 Aug / 2006
// https://sites.google.com/site/epslin4free/
// https://gitlab.com/jforsten/EpsLin/-/blob/master/EpsLin.c
// -------------------------------------------------
//  * File utility for Ensoniq samplers (EPS/ASR)
//
//  ------------------------------------------------------------------------
//  This program is free software; you can redistribute it and/or modify
//  it under the terms of the GNU General Public License as published by
//  the Free Software Foundation; either version 2 of the License, or
//  (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU General Public License for more details.
//
//  You should have received a copy of the GNU General Public License
//  along with this program; if not, write to the Free Software
//  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
//
// -------------------------------------------------------------------------
//
//  TO COMPILE:
//  ===========
//
//  Should compile in Linux, macOS, and Windows (Cygwin) just by typing:
//
//    gcc EpsLin_v1.56.c -o epslin
//
//  In Windows you have to install "fdrawcmd.sys" from
//         http://simonowen.com/fdrawcmd/
//
//  and get the header file from
//         http://simonowen.com/fdrawcmd/fdrawcmd.h
//
//  and put it in the same directory as the EpsLin source.
//
//  HISTORY
//  =======
//
//  v9.99: [FUTURE]
//       - Optional "allowed" devices list to minimize
//         unintentional writes to devices like system
//         hard disk etc.. for Format and ImageCopy
//         THIS COULD SAVE YOUR DAY (or even two)..!
//       - Check mode and only EFE erase/put use the
//         'I' write to check if 's' media type..
//       - Use 's' media type in Get and in GetFat/SetFat
//
// vX.XX: [FUTURE]
//       - TODO: allow a sector offset to be supplied; needed to
//               handle direct access of SCSI2SD-ready SD cards
//       - TODO: check for Ensoniq volume signatures prior to any
//               non-Format related routines
//       - TODO: add recursive mode for GetEFE
//       - TODO: create named sub-directories when GetEFE is used
//               such as 'root', etc. to hold EFEs on export
//
//  v1.56:
//       - Rudimentary support for TS10/TS12 file types.
//
//  v1.55:
//       - Support for 4GB partitions (i.e. prints the free blocks/bytes correctly)
//
//  v1.54:
//       - Multiple compiler warnings have been corrected.
//       - [macOS] Fixed "Abort trap: 6" bug on multi-part reporting.
//
//	v1.53:
//       - Fixed issue with "Part_xx" being appended to full path
//         rather than base filename.
//       - ASR SuperDisk is now allowed as a split target.
//
//	v1.52:
//       - Made newline characters compatible with Windows apps,
//         such as Notepad, et al.
//
//  v1.51:
//       - Fixed error with additional IsEFE checks from v1.47.
//       - Entries which can't be exported are now skipped by GetEFE.
//
//  v1.50:
//       - Added preliminary macOS support, although issues may exist.
//
//  v1.47:
//       - Added handling for EFEs with "/" in Ensoniq filename.
//       - Fixed crash in PutEFE when directory full (39th entry).
//       - Improved wildcard/globbing usage, although still not
//         100% case-insensitive under Windows, as is ideal.
//       - Null sector no longer used for vanity message, etc.
//       - Improved EFE/EFA/INS checking before PutEFE is allowed.
//       - Added INS extension support as an alias for EFE.
//       - Added Directory and Disk Information mode (read-only).
//       - Show usage help when '?' or unknown arguments used.
//       - Show usage help when run without arguments rather than
//         than showing potential "fdrawcmd.sys" error.
//
//  v1.46:
//       - [Windows] Cygwin component in non-contiguous portion
//         of the GetEFEs routine caused *some* EFEs not to extract
//         properly; routine was given an overhaul.
//       - Corrected SuperDisk support in PutEFE/GetMedia/EraseEFEs.
//       - Removed path from filename when printing report.
//
//  v1.45: (forked by Thomas Arashikage)
//       - [Windows] Tweaks to help compile under Cygwin.
//       - [Windows] Fixed FAT block calculation in GetEFE and GetInfo,
//                   as values could sometimes be off by one!
//       - [Windows] ReadBlock function altered to avoid abort on error.
//       - [Windows] Too restrictive permissions on newly created
//                   files (IMG, EFE, EDE, et al) were lessened.
//       - Corrected disk label size and default string.
//       - Added ASR-Macro to identified file types.
//       - Added SuperDisk (255 block) support for EPS16 and ASR which
//         is only applicable with HFEs under floppy emulators.
//
//  v1.42:
//       - [Windows] Had to optimize the I/O functions involved
//         when EFEs are GET/ERASED/PUT from/to media. This increased
//         the run time memory consumption, as the whole FAT
//         table are loaded to memory in order to avoid
//         seeks in CD-ROM (/dev/scd) and to write Iomega
//		     Zip drives which don't support single byte writes.
//         As the load/save time of the FAT table depends on the size
//         of the media, it _might_ take quite a long time for some media,
//         thus making the get/put/erase slow. As the Zip drive is the only
//	       device to test this, it happens to take only 2 seconds to
//         read+write the table, so it's quite reasonable.
//         If you send me a SCSI device, that is very slow for this reason,
//         I'll try to optimize the functions more - until that,
//         for me it's fast enough.. ;-)
//       - Options that accept parameter 'a' (= all), now starts
//         at idx 1 (not 0 as previous versions).
//       - Added progress info when EFEs are put/get.
//
//  v1.41:
//       - [Windows] Added support for /dev/scd layer in Cygwin..
//         Since the seeks are possible only in 2048 byte multiples
//         had to make some mods to ReadBlock etc. functions.
//         Minor penalties in performance..
//
//  v1.40: NOW PORTED TO WINDOWS!!
//       - Uses Simon Owens "fdrawcmd.sys" (http://simonowen.com/fdrawcmd/)
//         driver for low-level floppy access. Thanks Simon!
//       - Minor differences between Cygwin (Win32) and Linux in command
//         line arguments (for ex. Cygwin requires allways parameter for -p)
//       - Should support also SCSI devices through Cygwin layer
//       - Some minor fixes
//
//  v1.37:
//       - Fixed nasty bug in dir-argument (-d) parsing, that
//         sometimes leads an error "ERROR: Index '0' is not a directory!".
//         Hopefully now solved..
//       - More investigation had to be done to find out how EPS knows, when to
//         load Song (instruments has the mask,that tells what location to load -
//         for song there are no such info). It seems that if index is 0, it is
//         not counted as a valid song, so no song data is loaded.
//         The BankInfo function is modified based on that knowledge.
//
//         BTW: You can make deeper dir structures with EPS than banks can handle, so..
//              don't do it if you want to use files in those dirs with banks.. :-)
//
//       - Minor changes to BankInfo output. Paths starts with '/' and ends with no '/'
//
//
//  v1.36:
//       - Option to join multifile EFEs to single EFE file
//
//  v1.35:
//       - Added missing CR,LF,EOF bytes to EFE header (cosmetic)
//       - Option to show info from Ensoniq Bank EFE
//       - Option to split EFE to multifile parts added
//       - Option to print directory listing in compact mode to make the
//         parsing for external programs easier.
//       - Some code clean-ups...
//
//  v1.34:
//        - Support for Multi Files (ie. instruments, that don't fit in one floppy)
//        - Fixed (new) gcc errors
//
//  NOTES!
//  ======
//
//  * Some _commercial_ EPS/ASR tools corrupts the FAT.. You should avoid
//    those programs.. IF you have to use them, please at least check
//    the disks and image-files before use with EpsLin 'check' option (-C).
//    If you use those corrupted disk/images you may lose data!!
//
//   TODO:
//   =====
//
//   [CYGWIN]:
//   !! PutEFE doesn't work without idx number.. It's the Optget that
//      doesn't support optional arguments, so we'll wait for proper version...
//
//   [GENERAL]
//
//	 !! Format -fi optimize (now redundancy in allocated fat_block write)
//
//   !! MkDir max level.. (Bank can load files only max 11-level deep dirs)
//
//   !! Fix MKDIR Kludge in PutEFE...
//
//   !! Using Floppy with ReadImage sometimes mess up the FD controller !?
//
//   !! Add 'image copy' -feature (ie. make it possible to transfer
//      data in SCSI HD <-> ZIP, Zip requires '0x6d' at first byte in disk)
//
//   ! WAV to EFE & EFE to WAV conversions.
//
//   ! In EPS, the OS has to be in one contiguous part
//     * ASR doesn't mind...
//
//   - Dir-transfer function (copy files recursively..)
//     Useful to transfer whole dir structures from medium to an another.
//     (Must take care of changing SCSI-ID in Bank-files ?)
//
//   - Erase: Recurse Dirs !!
//
//   - Format_n_Write -support (?!)
//

// Uncomment to enter debug state...
// #define DEBUG

#include <ctype.h>
#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <libgen.h>
#include <dirent.h>

#ifdef __APPLE__
  #include <sys/uio.h>			// equivalent of <sys/io.h>
#elif __CYGWIN__
  #include <sys/uio.h>			// equivalent of <sys/io.h>
  #include <windows.h>
  #include "fdrawcmd.h"			// floppy drive support -- from http://simonowen.com/fdrawcmd/fdrawcmd.h
#else   // Linux
  #include <sys/io.h>
  #include <linux/fd.h>			// floppy drive support
  #include <linux/fdreg.h>		// floppy drive support
#endif

#ifdef __CYGWIN__				// Windows
	// do nothing
#else   						// Linux and macOS
	#define O_BINARY 0 			// In Windows, open is set to binary mode.
								// In Linux, this is not defined so set it to 0
								// (this value is ORed, so no harm is done..)
#endif

#ifdef __CYGWIN__
#define VERSION     "v1.55 (Beta)"
#elif __APPLE__
#define VERSION     "v1.55 (Beta)"
#else   // Linux
#define VERSION     "v1.55"
#endif

// This idea is too close to commercial "vanity" spam, so has been reverted to classic 0x6D/0xB6 fill pattern.
// Code only left for illustration purposes.
#ifdef __CYGWIN__
#define FIRST_BLOCK_MESSAGE "Created with EpsLin for Windows"
#else
#define FIRST_BLOCK_MESSAGE "Created with EpsLin for Linux"
#endif

#define BLOCK_SIZE      512				// amount of bytes per block
#define ID_BLOCK          1				// ID block is 1 because block 0 is null (0x6D/0xB6 filler)
#define DISK_LABEL_SIZE   7				// disk label is contained within ID block

#define OS_BLOCK          2				// OS block comes directly after ID block

#define DIR_START_BLOCK   3				// DR area comes directly after OS block
#define DIR_BLOCKS        2				// 1024 bytes for entire directory (DR)
#define DIR_END_BLOCK     4				// DR area consists of blocks 3 and 4

#define EFE_SIZE                26		// each directory entry is 26 bytes
#define MAX_NUM_OF_DIR_ENTRIES  39		// 1024 bytes in directory, so only 39 entries possible...
                                        // ...but zero indexed, so 0~38
#define MAX_DIR_DEPTH    10             // maximum amount of nesting

#define FAT_START_BLOCK      5			// FAT comes directly after DR area, but there is a variable amount
										// of FAT blocks; amount depends on capacity of specific volume
#define FAT_ENTRIES_PER_BLK	170			// 170 FAT entries allowed in each FAT block

#define MAX_DISK_SECT       20			// ASR uses 20 sectors per track, EPS/EPS16 uses 10 sectors

#define EPS_IMAGE_SIZE      819200		// size in bytes of EPS/EPS16 800K DD diskettes
#define E16_SD_IMAGE_SIZE  2611200		// size in bytes of EPS16 2550K "SuperDisk" images
#define ASR_IMAGE_SIZE     1638400		// size in bytes of ASR 1600K HD diskettes
#define ASR_SD_IMAGE_SIZE  5222400		// size in bytes of ASR 5100K "SuperDisk" images

// Buffer size for image copy
#define IMAGE_COPY_BUFFER_BLOCKS  100

#define DEFAULT_DISK_LABEL "DISK000"	// seven characters max

#define EDE_LABEL  "EPS-16 Disk"
#define EDE_SKIP_START     0xA0
#define EDE_SKIP_SIZE       200
#define EDE_ID             0x03

#define EDA_LABEL  "ASR-10 Disk"
#define EDA_SKIP_START     0x60
#define EDA_SKIP_SIZE       400
#define EDA_ID             0xCB

// Imagefile types
#define EPS_TYPE              'e'
#define E16_SD_TYPE           's'
#define ASR_SD_TYPE           'S'
#define ASR_TYPE              'a'
#define GKH_TYPE              'g'
#define EDE_TYPE              'E'
#define EDA_TYPE              'A'
#define OTHER_TYPE            'o'

//Modes for Bank Info
#define MODE_EPS 4
#define MODE_E16 23
#define MODE_ASR 30

// OS version info offsets (in EFE)
#define EPS_OS_POS 0x3A8
#define E16_OS_POS 0x390
#define ASR_OS_POS 0x6F2

// Modes
#define NONE    0
#define READ    1
#define WRITE   2
#define GET     3
#define PUT     4
#define ERASE   5
#define MKDIR   6
#define FORMAT  7
#define DIRLIST 8
#define TEST   99

// Print modes
#define HUMAN_READABLE 0
#define COMPUTER_READABLE 1

// Return values
#define ERR -1
#define OK   0

// Error print-out & exit
#ifdef DEBUG
#define EEXIT(args)  (fprintf(stderr,"(line: %d) ",__LINE__), fprintf args, exit(ERR))
#else
#define EEXIT(args)  (fprintf args, exit(ERR))
#endif

// File permissions
#ifdef __CYGWIN__           // Windows
#define FILE_RIGHTS 0777    // all can read, write and execute
#else                       // Linux and macOS
#define FILE_RIGHTS 0700    // owner can read, write and execute
#endif

// For 'getopt'
// Next two lines generate "redeclared without dllimport" warnings under CYGWIN, but apparently harmless.
extern char *optarg;
extern int optind, opterr, optopt;

// Datatype for floppy disk access
#ifdef __CYGWIN__
typedef HANDLE FD_HANDLE;
#else // Linux and macOS
typedef int FD_HANDLE;
#endif

#ifdef __CYGWIN__
char* LastError ()
{
  static char sz[256];
  FormatMessage(FORMAT_MESSAGE_FROM_SYSTEM | FORMAT_MESSAGE_IGNORE_INSERTS, NULL, GetLastError(),
		MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT), sz, sizeof(sz), NULL);
  return GetLastError() ? sz : "no error";
}
#endif

// Temp-file name
static char tmp_file[13] = "EpsLinXXXXXX";
//static char tmp_file[64];

// Declaration of ReadBlocks
int ReadBlocks(char media_type, FD_HANDLE fd, int file, unsigned int start_block,
	       unsigned int length, unsigned char *buffer);

// Temp-file cleanup -function (called by 'atexit')
static void CleanTmpFile(void) {
  unlink(tmp_file);
}

// EPS/ASR-file types
static char *EpsTypes[50]={
  //  0         1         2         3         4         5         6         7         8         9
  "(empty)","EPS-OS ","DIR/   ","Instr  ","EPS-Bnk","EPS-Seq","EPS-Sng","EPS-Sys",".. /   ","EPS-Mac",

  // 10        11        12        13        14        15        16        17        18        19
  "       ","       ","       ","       ","       ","       ","       ","       ","       ","       ",

  // 20        21        22        23        24        25        26        27        28        29
  "       ","       ","       ","E16-Bnk","E16-Eff","E16-Seq","E16-Sng","E16-OS ","ASR-Seq","ASR-Sng",

  // 30        31        32        33        34        35        36        37        38        39
  "ASR-Bnk","ASR-Trk","ASR-OS ","ASR-Eff","ASR-Mac","TS-6Pro","TS-60Pg","TS120Pg","TS-1Pre","TS-60Ps",
  
  // 40        41        42        43        44        45        46        47        48        49
  "TS120Ps","TS-1Seq","TS30Seq","TS60Seq","ENS44xx","ENS45xx","ENS46xx","ENS47xx","ENS48xx","ENS49xx",
  
};

// 00 (0x00) = Unused/Blank/Empty
// 01 (0x01) = EPS (original/classic) Operating System
// 02 (0x02) = Sub-Directory
// 03 (0x03) = EPS Individual Instrument File
// 04 (0x04) = EPS Bank of Sounds
// 05 (0x05) = EPS Sequence File
// 06 (0x06) = EPS Song File
// 07 (0x07) = EPS System Exclusive File
// 08 (0x08) = Pointer to Parent Directory
// 09 (0x09) = EPS Macro File
// ...missing entries are SD-1/VFX-SD only, so not applicable to ASR/EPS...
// 23 (0x17) = EPS-16 Plus Bank File
// 24 (0x18) = EPS-16 Plus Effect File
// 25 (0x19) = EPS-16 Plus Sequence File
// 26 (0x1A) = EPS-16 Plus Song File
// 27 (0x1B) = EPS-16 Plus Operating System
// 28 (0x1C) = ASR-10 Sequence File
// 29 (0x1D) = ASR-10 Song File
// 30 (0x1E) = ASR-10 Bank File
// 31 (0x1F) = ASR-10 Audio Track
// 32 (0x20) = ASR-10 Operating System
// 33 (0x21) = ASR-10 Effect File
// 34 (0x22) = ASR-10 Macro File / TS "1-PROGRAM" File (strange that there's a number overlap...)
// 35 (0x23) = TS "6-PROGRAMS" File
// 36 (0x24) = TS "60-PROGRAMS" File
// 37 (0x25) = TS "120-PROGRAMS" File
// 38 (0x26) = TS "1-PRESET" File
// 39 (0x27) = TS "60-PRESETS" File
// 40 (0x28) = TS "120-PRESETS" File
// 41 (0x29) = TS "1-SEQ/SONG" File
// 42 (0x2A) = TS "30-SEQ/SONGS" File
// 43 (0x2B) = TS "60-SEQ/SONGS" File


//////////////
// ShowUsage
void ShowUsage()
{
  printf("\r\nEpsLin Neo %s -- open source Ensoniq EPS/ASR file and disk utility \r\n", VERSION);
  printf("==============================================================================\r\n");
  printf("\r\nUsage: epslin [options] [imagefile or device] [EFE #0] [EFE #1] ... [EFE #N]\r\n\r\n");
  printf("Options:\r\n-------- \r\n\r\n");
  printf("   -r           Read image from disk. (Disk type (EPS/ASR) is autodetected!)\r\n");
  printf("                File extension (IMG/EDE/EDA) selects the format.\r\n\r\n");

  printf("   -w           Write image to disk. (Disk type (EPS/ASR) is autodetected!)\r\n");
  printf("                File extension (IMG/GKH/EDE/EDA) selects the format.\r\n\r\n");

  printf("   -fe,-fa,-fi  Format disk/image/device (a=ASR, e=EPS, i=image/device)\r\n");
  printf("                Use '-l' option to define disk label.\r\n");
  printf("                If imagefile doesn't exist, it will be created. \r\n");
  printf("                Image size is then needed as an last argument.\r\n");
  printf("                Size is in bytes ('K' and 'M' can be used as a suffix)\r\n");
  printf("                If EPS/ASR disk image is wanted, use size 'eps' or 'asr'\r\n");
  printf("                instead of numeric values!! See examples..\r\n\r\n");

  printf("      Examples: 'epslin -fe'                   : Format EPS floppy\r\n");
  printf("                'epslin -fa'                   : Format ASR floppy\r\n");
  printf("                'epslin -fi epsdisk.img eps'   : Create EPS disk image\r\n");
  printf("                'epslin -fi asrdisk.img asr'   : Create ASR disk image\r\n");
  printf("                'epslin -fi e16supr.img e16sd' : Create EPS16 SuperDisk image\r\n");
  printf("                'epslin -fi asrsupr.img asrsd' : Create ASR SuperDisk image\r\n");
  printf("                'epslin -fi MyImage.img'       : Format MyImage.img\r\n");
  printf("                                                 NOTE: File exists!\r\n");
  printf("                'epslin -fi MyCDROM.img 650M'  : Create and format\r\n");
  printf("                                                 file size 650MB\r\n");
  printf("                'epslin -l EpsHD -fi /dev/sda' : Format SCSI disk\r\n");
  printf("                                               : with label 'EpsHD'\r\n\r\n");

  printf("   -c           Convert imagefile from one format to another.\r\n");
  printf("                Supported conversions:\r\n");
  printf("                                               .img -> ede (EPS)\r\n");
  printf("                                               .img -> eda (ASR)\r\n");
  printf("                                               .gkh -> img (EPS)\r\n");
  printf("                                               .ede -> img (EPS)\r\n");
  printf("                                               .eda -> img (ASR)\r\n");
  printf("                Examples: 'epslin -c my_disk.img my_disk.ede'\r\n\r\n");

  printf("   -g index_list \r\n");
  printf("                Get EFE(s) from image/dev.\r\n");
  printf("                Examples: -g1,2,4   : EFEs 1,2 and 4.\r\n");
  printf("                          -g10-20   : from 10 to 20.\r\n");
  printf("                          -g10-     : from 10 to end.\r\n");
  printf("                          -g1,3-5,8 : 1,3 to 5, and 8.\r\n");
  printf("                          -ga       : All from that dir.\r\n\r\n");
#ifdef __CYGWIN__
  printf("   -p start_index \r\n");
  printf("                Put EFE(s) to image/dev. The EFE is saved to the\r\n");
  printf("                first empty index found. The search of empty index\r\n");
  printf("                can be set to start at start_index.\r\n");
  printf("                The EFE files must be defined after image file.\r\n");
  printf("                Examples: -p1  EFE_files.efe : Put EFE in the idx 1 or\r\n");
  printf("                                               first empty index.\r\n");
  printf("                          -p1  all           : Put all EFEs found in\r\n");
  printf("                                               the current dir.\r\n");
  printf("                          -p0 os_file.efe    : Put Operating System\r\n");
  printf("                                               to index 0.\r\n\r\n");

#else // Linux and macOS
  printf("   -p [start_index] \r\n");
  printf("                Put EFE(s) to image/dev. The EFE is saved to the\r\n");
  printf("                first empty index found. The search of empty index\r\n");
  printf("                can be set to start at start_index (default=1).\r\n");
  printf("                The EFE files must be defined after image file.\r\n");
  printf("                Examples: -p  EFE_files.efe  : Put EFE in the first \r\n");
  printf("                                               empty index.\r\n");
  printf("                          -p  all            : Put all EFEs found in\r\n");
  printf("                                               the current dir.\r\n");
  printf("                          -p0 os_file.efe    : Put Operating System\r\n");
  printf("                                               to index 0.\r\n\r\n");
#endif
  printf("   -e index_list \r\n");
  printf("                Erase EFE(s) from image/dev.\r\n\r\n");

  printf("   -D           Shows directory and disk information, such as EFE listing and \r\n");
  printf("                amount of used and free space in blocks and bytes. \r\n");
  printf("                Example: -D FMsynths.img \r\n");
  printf("                Example: -D drums.gkh \r\n\r\n");

  printf("   -d path      Directory definition for most operations. \r\n");
  printf("                Use index number for sub-directory. \r\n");
  printf("                Example: 'epslin -d2 -ga DX7stabs.img' \r\n\r\n");

  printf("                For nested sub-folders, use forward-slashes. \r\n");
  printf("                Example: -d12/4/7 \r\n\r\n");

  printf("   -m dir_name  Make directory.\r\n\r\n");

  printf("   -C level     Check the disk/image. Gives detailed info about the \r\n");
  printf("                low-level technical structure of the disk/image.\r\n");
  printf("                Level can be either 0 or 1.\r\n\r\n");

  printf("   -s EFE_to_split slice_type\r\n");
  printf("                Split a big EFE into smaller pieces.\r\n");
  printf("                Example: -s big.efe eps       : Slices to fit EPS DD size \r\n");
  printf("                Example: -s big.efe asr       : Slices to fit ASR HD size \r\n\r\n");

  printf("   -b bank.efe  Bank info. Prints useful(?) inside info about bank EFE \r\n\r\n");

  printf("   -P           Parse-friendly output. Use with GUI/frontend software \r\n\r\n");
  printf("image_file = Ensoniq EPS/EPS16/ASR-type disk image file \r\n\r\n");
}

///////////////
// ParseRange
void ParseRange(char *optarg, char process_EFE[MAX_NUM_OF_DIR_ENTRIES])
{
  size_t ssize;
  char tmp_str[80];
  int from_EFE,to_EFE,i;

  strcpy(tmp_str,optarg);

  ssize = strspn(tmp_str,"0123456789");
  tmp_str[ssize]='\0';
  from_EFE= atoi(tmp_str);

  if(strlen(optarg)== ssize+1) {
    to_EFE=MAX_NUM_OF_DIR_ENTRIES-1;
  } else {
    to_EFE= atoi(tmp_str+ssize+1);
  }
  // Mark the range of EFEs
  for(i=from_EFE;i<=to_EFE;i++) process_EFE[i]=1;

}

////////////////
// ParseList
void ParseList(char *optarg, char process_EFE[MAX_NUM_OF_DIR_ENTRIES])
{
  size_t ssize;
  char tmp_str[80];
  int j;

  strcpy(tmp_str,optarg);
  j=0;
  // Slice the argument using ',' as a separator.
  while((ssize = strspn(tmp_str+j,"0123456789-")) != 0) {
    tmp_str[ssize+j]='\0';
    // List element is 'range'
    if((index(tmp_str+j,'-')) != NULL) {
      ParseRange(tmp_str+j,process_EFE);
    } else {
      process_EFE[atoi(tmp_str+j)] = 1;
    }
    j=j+(ssize+1);
  }
}

/////////////////////////
// ParseEntry
void ParseEntry(char *optarg, char process_EFE[MAX_NUM_OF_DIR_ENTRIES])
{
  char *idx_new;
  int i;

  // All?
  if(strcmp(optarg,"a")==0) {
    //Mark all
    for(i=1;i < MAX_NUM_OF_DIR_ENTRIES; i++) process_EFE[i]=1;
  } else {
    // List ?
    if((idx_new=index(optarg,',')) == NULL) {
      // Range ?
      if(index(optarg,'-')) {
	ParseRange(optarg,process_EFE);
      } else {
	// One number - Mark it
	process_EFE[atoi(optarg)]=1;
      }
    } else {
      ParseList(optarg,process_EFE);
    }
  }

}

//////////////////////
// ParseDir
int ParseDir(char *dirpath_str, unsigned int *DirPath, unsigned int *subdir_cnt)
{

  char *idx_new, *idx, dir_str[80];

  // Validity check for 'dirpath_str' ie. can't
  // be over 70 characters (even that's too much!)
  if(strlen(dirpath_str) > 70) {
    EEXIT((stderr,"ERROR: Invalid directory path '%s'.\r\n",dirpath_str));
  }

  // Clear the 'dir_str'-buffer so that
  // parsing doesn't fail if buffer contains
  // character '/' at the "right" place.. (ie. bug fix :-)
  dir_str[strlen(dirpath_str)+1]= 0;

  // Make a copy of path string
  strcpy(dir_str,dirpath_str);

  // Check if path starts with '/'
  if(dir_str[0] == '/') {
    if(dir_str[1] == '\0') return(OK); else dir_str[0]=' ';
  }

  *subdir_cnt=0;

  // Parse 'path'
  if(dir_str[strlen(dir_str)-1] != '/') {
    dir_str[strlen(dir_str)]='/';
    dir_str[strlen(dir_str)+1]='\0';
  }

  idx= dir_str;
  while((idx_new= (char *) index(idx,'/')) != NULL) {
    *idx_new= '\0';
    DirPath[*subdir_cnt]=atoi(idx);
    idx= idx_new+1;
    (*subdir_cnt)++;
  }
  return(OK);
}

////////////////////
// Name to DosName
// ---------------
// Some characters allowed by Ensoniq are not allowed by PC operating systems
// to exist in a filename (such as asterisk, as it is used as a wildcard).

void DosName(register char *dosname, char *name)
{
  register char *p;

  // Correct "invalid" character(s) within Ensoniq filename using substitution.
  strcpy(dosname,name);
  while((p=(char *) strchr(dosname,'*'))!=NULL) {
	// substitute '#' when '*' was used in Ensoniq file
    *p='#';
  }

  while((p=(char *) strchr(dosname,'/'))!=NULL) {
	// substitute '^' when '/' was used in Ensoniq file
    *p='^';
  }

  // Uncomment if 'space' to '_' -conversion needed
  // Not generally needed as spaces can exist in Windows filenames when quotes are in use.
  /*
    while((p=strchr(dosname,' '))!=NULL) {
    *p='_';
    }
  */

  // Add .efe file extension to corrected filename.
   strcat(dosname,".efe");

}

///////////////////////////
// Print the Directory List
// ------------------------
// Shows all EFEs stored on disk and how much space is used and free.
// The parameters passed to this function are
void PrintDir(unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE], unsigned int mode,
	      char process_EFE[MAX_NUM_OF_DIR_ENTRIES], char in_file[FILENAME_MAX],
	      char media_type, char *DiskLabel, unsigned int  free_blks, unsigned int used_blks,
	      int printmode)
{
  unsigned int size, cont, start;
  unsigned int type, real_type, j, k;
  char name[13],dosname[17];
  char media[FILENAME_MAX];
  char type_text[9];

  // Create variable to hold just the filename without path.
  char *bname;
  // Use 'basename' to return just the filename of the input file.
  bname = basename(in_file);

  switch (media_type)
    {
    case 'f':
      strcpy(media,"FILE: ");
      strcat(media,bname);
      break;
    case 'e':
      strcpy(media,"EPS DISK ");
      //strcat(media,DiskLabel);
      break;
    case 'a':
      strcpy(media,"ASR DISK ");
      //strcat(media,DiskLabel);
      break;
    }

  // Print DirectoryList
  // ===================

  if(printmode== HUMAN_READABLE) {
    printf("\r\n------------------------------------------+---------------------------------+\r\n");
    printf(" Disk Label: %-28s |", DiskLabel);
    printf(" %-31s |\r\n", media);
    printf("------+----------+--------------+---------+------------------+--------------+\r\n");
    printf("  Idx |Type      | Name         |Blocks   | FileName         | FileSize     |\r\n");
    printf("------+----------+--------------+---------+------------------+--------------+\r\n");
  } else {
    //Computer readable: Label, media, used block, used bytes, free blocks, free bytes, total blocks, total bytes
    printf("%s,%s,%d,%lu,%lu,%lu,%lu,%lu\r\n", DiskLabel, media, used_blks, (unsigned long) (used_blks)*512, free_blks, (unsigned long) (free_blks)*512,  free_blks+used_blks, (unsigned long)(free_blks+used_blks)*512);
  }

  for(j=0;j<MAX_NUM_OF_DIR_ENTRIES;j++){

    //Name
    for(k=0;k<12;k++) {
      name[k]=EFE[j][k+2];
    }
    name[12]=0;

    DosName(dosname,name);

    size =(unsigned int)  ((EFE[j][14] << 8) + EFE[j][15]);
    cont =(unsigned int)  ((EFE[j][16] << 8) + EFE[j][17]);
    start=(unsigned long) ((EFE[j][18] << 24)+ (EFE[j][19] << 16) +
			   (EFE[j][20] << 8 ) + EFE[j][21]);
    type=EFE[j][1];
    real_type=type;

    // Check if type cannot possibly be known
    if(type>49) {
      type=49;
    }

    //if(1) {
    if(type!=0) {

      if(printmode == HUMAN_READABLE) {
	if(process_EFE[j] == 1) {
	  switch(mode)
	    {
	    case GET:
	      printf("<-");
	      break;

	    case PUT:
	    case MKDIR:
	      printf("->");
	      break;

	    case ERASE:
	      printf("!!");
	      break;

	    default:
	      break;
	    }
	} else {
	  printf("  ");
	}
      }

      if(printmode == HUMAN_READABLE) {
        if((type==2) || (type==8)) {
          printf(" %02d | %s  | %-12s |         |                  |              |\r\n",j,EpsTypes[type],name);
	       } else {
	  if(type!=0) {
	    strcpy(type_text,EpsTypes[type]);
      // if EFE[j][22] is not 0 then it's part of a multi-file
	    if( EFE[j][22] != 0) {
	      type_text[5]='\0';
	      printf(" %02d | %s(%2d)| %-12s | %7d | %s | %12ld |\r\n",j,type_text,EFE[j][22],name,size,dosname, (unsigned long) (size+1)*512);
	    } else {
	      printf(" %02d | %s  | %-12s | %7d | %s | %12ld |\r\n",j,type_text,name ,size,dosname, (unsigned long) (size+1)*512);
	    }
	  }
	} // else
      } else {
	// Computer readable
	printf("%d,%s,%d,%s,%d,%d,%s,%ld\r\n",j, EpsTypes[type], real_type, name,EFE[j][22], size, dosname, (unsigned long) (size+1)*512);
      }

      // This line is for debugging. Uncomment it if needed
      //printf(" %02d | %s(%d)  | %-12s | %4d | start=%d(%x) , cont=%d(%x) |\r\n",j,EpsTypes[type],real_type,name ,size, start,start,cont,cont);


    }
    //else if (printmode == COMPUTER_READABLE) {
    // If empty dir entry in this index, print "null" line for easier computer parsing...
    //   printf("%d,%s,%d,%s,%d,%d,%s,%ld\r\n",j, "(empty)",0 ,"", 0,0,"",0);
    //}


  }

  if(printmode == HUMAN_READABLE) {
    printf("------+----------+--------------+---------+---------------------------------+\r\n");
    printf(" Used:  %23lu Blocks    |  Used: %16lu Bytes   |\r\n", used_blks, (unsigned long) (used_blks)*512);
    printf(" Free:  %23lu Blocks    |  Free: %16lu Bytes   |\r\n", free_blks, (unsigned long) (free_blks)*512);
    printf("----------------------------------------------------------------------------+\r\n");
    printf(" Total: %23lu Blocks    |  Total:%16lu Bytes   |\r\n", free_blks+used_blks, (unsigned long) (free_blks+used_blks)*512);
    printf("----------------------------------------------------------------------------+\r\n\r\n");
  }

}

/////////////////////////////////////
// PrintBankInfo
// =============
// - Prints the structure of bank including
//   instruments and songs.
int PrintBankInfo(char filename[FILENAME_MAX], int printmode)
{
  int mode,count;
  int instValid[8];
  int effectFound=0;
  int fd;
  int i,j,k;
  unsigned char data[1024];

  if(printmode == COMPUTER_READABLE) {
    // COMPUTER READABLE


    //Open & Read
    if( (fd=open(filename,  O_RDONLY | O_BINARY, 0)) <= 0) {
      printf("1\r\n");
      return(1);
    }
    if((count=read(fd,data,0x222)) < 0x222) {
      printf("1\r\n");
      return(1);
    }

    // Get Bank type
    if((data[0x32] != 4) &&  (data[0x32] != 23) && (data[0x32] != 30)) {
      printf("2\r\n");
      return(1);
    }

    // OK
    printf("0\r\n");

    // Bank Type
    mode=data[0x32];
    printf("%d\r\n",mode);

    // Check Num of Blocks
    if(data[0x35] > 3) {
      effectFound = 1;
    }


    // Bank Name
    for(i=0x208;i<0x220;i=i+2) {
      printf("%c",data[i]);
    }
    //Mask
    printf("\r\n%d\r\n",data[0x220]);
    instValid[7] = (data[0x220] >> 7) & 0x01;
    instValid[6] = (data[0x220] >> 6) & 0x01;
    instValid[5] = (data[0x220] >> 5) & 0x01;
    instValid[4] = (data[0x220] >> 4) & 0x01;
    instValid[3] = (data[0x220] >> 3) & 0x01;
    instValid[2] = (data[0x220] >> 2) & 0x01;
    instValid[1] = (data[0x220] >> 1) & 0x01;
    instValid[0] =  data[0x220]       & 0x01;


    for(j=0;j<9;j++) {

      //eps
      if(mode==MODE_EPS) {
	read(fd,data,16);
      } else if(mode==MODE_E16) {
	read(fd,data,16);
      } else {
	read(fd,data,28);
      }

      // Valid instrument?
      if(j<8) {

	if(!instValid[j]) {
	  printf("0\r\n");
	  continue;
	}
      } else {
	// Valid song ?
	if(data[4] == 0) {
	  printf("0\r\n");
	  continue;
	}
      }

      // Inst/Song info
      if(data[0] > 0x7f) {
	//Song?
	if(j==8) {
	  printf("0\r\n");
	} else {
	  // "Copy of" + Inst num
	  printf("2,%d\r\n",(data[0] & 0x0f)+1);
	}
      } else {

	//"Valid" + Path Depth
	printf("1,%d,",data[0]);
	// Device
	printf("%d,",data[2]);
	//Media Name (if any)
	if(mode==MODE_EPS) {
	  printf("<NONE>,");
	} else {
	  printf("%c%c%c%c%c%c%c,",
		 data[ 3],
		 data[ 5],
		 data[ 7],
		 data[ 9],
		 data[11],
		 data[13],
		 data[15]);
	}

	if(data[0] > 0) {
	  for(k=0;k<data[0];k++) {
	    printf("/%d",data[ 4+2*k]);
	  }
	  printf(",%d\r\n",data[4+2*k]);
	} else {
	  printf("/,%d\r\n",data[4]);
	}

      }
    }
    if(effectFound) {
      lseek(fd,0x800,0);
      read(fd,data,64);
      printf("1,%c%c%c%c%c%c%c%c%c%c%c%c\r\n",
	     data[10],
	     data[12],
	     data[14],
	     data[16],
	     data[18],
	     data[20],
	     data[22],
	     data[24],
	     data[26],
	     data[28],
	     data[30],
	     data[32]);

    } else {
      printf("0\r\n");
    }

  } else {
    // HUMAN READABLE

    if( (fd=open(filename,  O_RDONLY | O_BINARY, 0)) <= 0) {
      printf("ERROR: File not found!\r\n");
      return(1);
    }

    if( (count=read(fd,data,0x222)) < 0x222) {
      printf("ERROR: File read error!\r\n");
      return(1);
    }

    // Get Bank type
    switch (data[0x32]) {
    case 4:
      mode=MODE_EPS;
      printf("Bank type:EPS\r\n");
      break;
    case 0x17:
      mode=MODE_E16;
      printf("Bank type:EPS16+\r\n");
      break;
    case 0x1e:
      mode=MODE_ASR;
      printf("Bank type:ASR\r\n");
      break;
    default:
      printf("ERROR: Not an Ensoniq Bank file!\r\n");
      exit(1);
    }

    // Check Num of Blocks
    if(data[0x35] > 3) {
      effectFound = 1;
    }

    printf("Bank Name:");
    for(i=0x208;i<0x220;i=i+2) {
      printf("%c",data[i]);
    }
    printf("\r\n");
    printf("Inst Mask:0x%x (%d%d%d%d%d%d%d%d)\r\n",data[0x220],
	   (data[0x220] >> 7) & 0x01,
	   (data[0x220] >> 6) & 0x01,
	   (data[0x220] >> 5) & 0x01,
	   (data[0x220] >> 4) & 0x01,
	   (data[0x220] >> 3) & 0x01,
	   (data[0x220] >> 2) & 0x01,
	   (data[0x220] >> 1) & 0x01,
	   data[0x220] & 0x01);

    for(j=0;j<9;j++) {

      if(j==8) {
	printf("\r\nSONG\r\n");
      } else {
	printf("\r\nINST %d\r\n",j+1);
      }
      //eps
      if(mode==MODE_EPS) {
	read(fd,data,16);
      } else if(mode==MODE_E16) {
	read(fd,data,16);
      } else {
	read(fd,data,28);
      }

      if(data[0] >= 0x80) {
	if(j==8) {
	  printf("<NONE>\r\n");
	} else {
	  printf("Copy Of Inst: %d\r\n",(data[0] & 0x0f)+1);
	}
      } else if (data[0] == 0x7f) {
	printf("Deleted\r\n");
      } else {
	printf("Path Depth: %d (0x%x)\r\n",data[0],data[0]);
	printf("0xFF: 0x%x\r\n",data[1]);
	printf("Media (0=floppy, SCSI+1): 0x%x\r\n",data[2]);
	printf("Disk Label: %c%c%c%c%c%c%c\r\n",
	       data[ 3],
	       data[ 5],
	       data[ 7],
	       data[ 9],
	       data[11],
	       data[13],
	       data[15]);

	if(data[0] > 0) {
	  printf("Path:");
	  for(k=0;k<data[0];k++) {
	    printf("/%d",data[ 4+2*k]);
	  }
	  printf("\r\nInst Idx:%d\r\n",data[4+2*k]);
	} else {
	  printf("Inst Idx:%d\r\n",data[4]);
	}

      }
    }
    if(effectFound) {
      lseek(fd,0x800,0);
      read(fd,data,64);
      printf("\r\nEFFECT: %c%c%c%c%c%c%c%c%c%c%c%c\r\n\r\n",
	     data[10],
	     data[12],
	     data[14],
	     data[16],
	     data[18],
	     data[20],
	     data[22],
	     data[24],
	     data[26],
	     data[28],
	     data[30],
	     data[32]);
    }
  }
  return(0);
}


/////////////////////////////////
// Get FAT entry - use FAT table
unsigned int GetFatEntry(char media_type, unsigned char *DiskFAT, int file, unsigned int block)
{
  unsigned int fatsect, fatpos,tmp;
  unsigned char FatEntry[3];

  fatsect= (int) block / FAT_ENTRIES_PER_BLK;
  fatpos = block % FAT_ENTRIES_PER_BLK;

  if(media_type=='f') {
    // FILE ACCESS
#ifdef __CYGWIN__
    // To get /dev/scd work...
    { unsigned char tmp_buff[512];
    ReadBlocks(media_type,(FD_HANDLE) 0,file,(FAT_START_BLOCK+fatsect),1,tmp_buff);
    return((tmp_buff[fatpos*3] << 16) + (tmp_buff[fatpos*3+1] << 8) + tmp_buff[fatpos*3+2]);

    }
#else // Linux and macOS
    if(lseek(file,(FAT_START_BLOCK+fatsect)*BLOCK_SIZE+fatpos*3, SEEK_SET) == -1) {
      printf("ERROR in seek\r\n");
    }
    if(read(file,FatEntry,3) == 0) {
      printf("ERROR in read\r\n");
    }
    return((FatEntry[0] << 16) + (FatEntry[1] << 8) + FatEntry[2]);
#endif

} else { // media type is not file access
    // DISK ACCESS - uses FAT-table
    tmp = (fatsect*BLOCK_SIZE) + fatpos*3;
    return((DiskFAT[tmp] << 16) + (DiskFAT[tmp+1] << 8) + DiskFAT[tmp+2]);
  }
}

/////////////////////
// PutFatEntry
int PutFatEntry(char media_type, unsigned char *DiskFAT, int file,
		unsigned int block, unsigned int fatval)
{
  unsigned int fatsect, fatpos,tmp;
  unsigned char FatEntry[3];

  fatsect= (int) block / FAT_ENTRIES_PER_BLK;
  fatpos = block % FAT_ENTRIES_PER_BLK;

  FatEntry[2] = fatval  &  0x000000FF;
  FatEntry[1] = (fatval >> 8) & 0x000000FF;
  FatEntry[0] = (fatval >> 16) & 0x000000FF;

  if(media_type=='f') {
    // file access
    lseek(file,(FAT_START_BLOCK+fatsect)*BLOCK_SIZE+fatpos*3, SEEK_SET);
    write(file,FatEntry,3);
    return(OK);

  } else {
    // disk access - uses FAT-table
    tmp = (fatsect*BLOCK_SIZE) + fatpos*3;
    memcpy(DiskFAT+tmp, FatEntry,3);
    return(OK);
  }
}

//////////////////////
// Convert MacFormat
// ===================
// - Convert really _stupid_ 'Mac'-format (ie. every '0x0a' is replaced by '0x0d0a')..
//   Why this even exists !?!?

int ConvertMacFormat(int *in, char *in_file)
{
  int out;
  //int c;
  unsigned int Hdr,i,prev;
  char temp_file[FILENAME_MAX];
  unsigned char *mem_pointer;
  struct stat stat_buf;

  lseek(*in,(long) 0,SEEK_SET);
  read(*in,&Hdr,4);
  lseek(*in,(long) 0,SEEK_SET);

  Hdr = Hdr & 0x00FFFFFF;
  if(Hdr == 0x0a0d0d) {

    mkstemp(temp_file);
    if((out =open(temp_file, O_RDWR | O_BINARY)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",temp_file));
    }
    unlink(temp_file);

    if(stat(in_file,&stat_buf) != 0) {
      EEXIT((stderr,"ERROR: Can't get the filesize!!\r\n"));
    }

    mem_pointer=malloc(stat_buf.st_size);
    if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

    read(*in,mem_pointer, stat_buf.st_size);

    // Find '0x0a' and copy fragments to file without proceeding '0x0d'

    prev = 0;
    for(i=0; i<stat_buf.st_size; i++) {
      if(mem_pointer[i] == 0x0a) {
	write(out,mem_pointer+prev,i - prev -1);
	prev = i;
      }
    }

    // if '0x0a' is last byte it has to write out separately..
    // Otherwise write whats left...
    if((i-1) != prev) {
      write(out,mem_pointer+prev,i - prev);
    } else {
      write(out,mem_pointer+prev,1);
    }

    free(mem_pointer);

    // Close original and give pointer to converted file
    close(*in);
    *in=out;

    return(OK);

  } else {
    return(ERR);
  }
}

//////////////////////
// ConvertToImageFile
// ------------------
// Convert EDA, EDE, and GKH to standard raw sector IMG
int ConvertToImage(char in_file[FILENAME_MAX], char out_file[FILENAME_MAX])
{
  int in, out;
  struct stat stat_buf;

  unsigned int i, j, skip_start, skip_size, num_of_tags, num_of_blks, img_length, img_offset;
  unsigned char buffer[BLOCK_SIZE], Data[BLOCK_SIZE], *mem_pointer, *SkipTable;
  char bits, *p;

  mem_pointer=NULL;

  if((in=open(in_file, O_RDONLY | O_BINARY)) < 0) {
    EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",in_file));
  }

  if((out=open(out_file, O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {
    EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",out_file));
  }

  if((p= (char *) rindex(in_file,'.')) != NULL) {
    p++;
    //printf("Extension: %s\r\n",p);

    if(strcasecmp(p,"gkh") == 0) {
      //printf("GKH file found\r\n");

      //// GKH ////
      if(stat(in_file,&stat_buf) != 0) {
		EEXIT((stderr,"ERROR: Can't get the filesize!!\r\n"));
      }

      lseek(in,(long) 0, SEEK_SET);
      read(in,Data,8);

      if(Data[4] != 'I') {
		EEXIT((stderr,"ERROR: GKH file in Motorola format is not supported!!\r\n"));
      }

      //num_of_tags = (Data[6] & 0x000000ff) + (Data[7] & 0x000000ff);
      num_of_tags = (unsigned int) (*((unsigned int *) (Data+6)) & 0x0000ffff);

      //printf("num_of_tags= %d\r\n",num_of_tags);

      for(i=0; i<num_of_tags; i++) {
	    read(in,Data,10);

		// DISKINFO-tag
		if(*Data == 0x0a) {
			num_of_blks = (unsigned int) ((*((unsigned int *) (Data+2)) & 0x0000ffff) *
						  (*((unsigned int *) (Data+4)) & 0x0000ffff) *
						  (*((unsigned int *) (Data+6)) & 0x0000ffff));
		//printf("num_of_blks = %d\r\n", num_of_blks);
	}

	// DISKINFO-tag
	if(*Data == 0x0b) {
	  img_length = (unsigned int) *((unsigned int *)(Data+2));
	  img_offset = (unsigned int) *((unsigned int *)(Data+6));
	  //printf("img_length = %d\r\n", img_length);
	  //printf("img_offset = %d\r\n", img_offset);
	}

    }

	  // GKH header is always fixed length of 58 bytes, so skip it.
      lseek(in,(long) img_offset, SEEK_SET);

	  // GKH is essentially raw sector IMG, so copy expected amount of
	  // data based upon total amount of expected blocks.
      for(i=0; i<num_of_blks;i++) {
		read(in,Data,BLOCK_SIZE);
		write(out,Data,BLOCK_SIZE);
      }

      // Get INFO after image
      // -- uncomment if INFO needed
      /*
	if(!feof(in)) {
	printf("\r\nInfo included in GKH file: \r\n");
	bits=fgetc(in);
	while (feof(in) == 0) {
	printf("%c",bits);
	bits=fgetc(in);
	}
	printf("\r\n");
	}
      */

    } else if ((strcasecmp(p,"ede") == 0) || (strcasecmp(p,"eda") == 0)) {

      //// EDE / EDA /////
	  //
	  // EDE/EDA are Giebler format which aims to reduce file size by eliminating any unused blocks.
	  // The first block in an EDE/EDA has a skip table which tells whether a certain block was used
	  // or skipped. Skipped blocks are padded out with 0x6D/0xB6 filler data, otherwise used blocks
	  // are treated just like raw sector IMGs.

      if (strcasecmp(p,"ede") == 0) {
	skip_start= EDE_SKIP_START;
	skip_size = EDE_SKIP_SIZE;
      } else {
	skip_start= EDA_SKIP_START;
	skip_size = EDA_SKIP_SIZE;
      }

      // Create a one block buffer of nothing but filler data.
	  // Essentially this assumes the current block has been skipped, but this
      // filler block is then ignored if the block was truly used.
      for(i=0; i<BLOCK_SIZE;i=i+2) {
		buffer[i  ]=0x6D;
		buffer[i+1]=0xB6;
      }

      // Check and convert if 'Mac'-format :-P is found
      if(ConvertMacFormat(&in, in_file) == OK) {
		printf("Warning: Macintosh generated EDx file found!\r\n");
      }

      mem_pointer=malloc(BLOCK_SIZE);
      if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
      SkipTable = mem_pointer + skip_start;

      // Read EDE/EDA skip table
      lseek(in, (long) 0, SEEK_SET);
      read(in,mem_pointer,BLOCK_SIZE);

      lseek(in, BLOCK_SIZE, SEEK_SET);

      for(i=0; i<skip_size;i++) {
		// get one byte from the skip table; each byte in the skip table
		// holds the skip-or-not value of 8 sequential blocks
		bits= SkipTable[i];

		// 8 bits per byte, so each bit holds the skip-or-not value of one block
		for(j=0;j<8;j++) {
			if(bits < 0) {
				// if block was skipped then write filler block
				write(out,buffer,BLOCK_SIZE);
			} else {
				// otherwise write entire block of genuine data
				read(in,Data,BLOCK_SIZE);
				write(out,Data,BLOCK_SIZE);
			}
			// rotate to next bit
			bits=bits << 1;
		} // for j -- ends when all 8 bits have been checked

      } // for i -- ends when entire skip table has been processed


    } else {
      // other extension - assume raw image
	  // could add extra header checks here for more robust handling
      //printf("No conversion!\r\n");
      free(mem_pointer);
      close(in);close(out);
      return(ERR);
    }
  } else {
    // Can't get file type
    //printf("No conversion!\r\n");
    free(mem_pointer);
    close(in); close(out);
    return(ERR);
  }

  //printf("conversion done!\r\n");
  free(mem_pointer);
  close(in); close(out);
  return(OK);
}

//////////////////////
// ConvertFromImage
// ----------------
// Takes raw sector IMG and converts to Giebler EDA/EDE or GKH...
// ...although GKH output is not currently supported.
int ConvertFromImage (char in_file[FILENAME_MAX], char out_file[FILENAME_MAX], char type)
{
  int in,out;
  unsigned char bits, *SkipTable, *mem_pointer, edx_id;
  char edx_label[12];
  unsigned int skip_size, skip_start,block, i,j;
  unsigned char Data[BLOCK_SIZE];

  edx_id = 0; skip_start = 0; skip_size = 0;

  switch (type)
    {
    case EDE_TYPE:
      skip_start= EDE_SKIP_START;
      skip_size = EDE_SKIP_SIZE;
      edx_id    = EDE_ID;
      strcpy(edx_label, EDE_LABEL);
      break;

    case EDA_TYPE:

      skip_start= EDA_SKIP_START;
      skip_size = EDA_SKIP_SIZE;
      edx_id    = EDA_ID;
      strcpy(edx_label, EDA_LABEL);
      break;

    case GKH_TYPE:
      EEXIT((stderr,"ERROR: GKH output not supported yet!\r\n"));

    default:
      EEXIT((stderr,"ERROR: Unsupported conversion!\r\n"));

    }

  //printf("RAW -> EDx conversion!!\r\n");

  if((in=open(in_file, O_RDONLY | O_BINARY)) < 0) {
    EEXIT((stderr,"ERROR: Couldn't open file '%s'.",in_file));

  }
  if((out=open(out_file, O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {
    EEXIT((stderr,"ERROR: Couldn't open file '%s'.",out_file));
  }

  mem_pointer = malloc(BLOCK_SIZE);
  if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

  SkipTable=mem_pointer+skip_start;

  // Construct EDx header
  // --------------------
  // Giebler has some particular formatting aside from just the skip table, so
  // write out the expected data before generating the actual skip table.

  // CR & LF
  mem_pointer[0]=0x0D;
  mem_pointer[1]=0x0A;

  // Spaces trough 0x02 - 0x4D
  for(i=0x02; i<0x4E;i++) {
    mem_pointer[i] = 0x20;
  }

  // Write EDE label
  strncpy((char *) (mem_pointer+2), edx_label, 11);

  // CR & LF
  mem_pointer[0x4E]=0x0D;
  mem_pointer[0x4F]=0x0A;

  // Spaces through 0x50 - skip_start
  for(i=0x50; i<skip_start;i++) {
    mem_pointer[i] = 0x20;
  }

  // CR & LF
  mem_pointer[skip_start-3]=0x0D;
  mem_pointer[skip_start-2]=0x0A;
  mem_pointer[skip_start-1]=0x1A;

  // Disktype ID
  mem_pointer[BLOCK_SIZE-1] = edx_id;
  // Write Header
  write(out,mem_pointer,BLOCK_SIZE);

  // Generate SkipTable
  // ------------------
  // EDA/EDE skip table is easy to generate because the Ensoniq FAT
  // already declares whether a block is empty or not, so just check
  // the FAT and set the proper bits within the corresponding bytes
  // in the skip table.
  block=0;
  // go through each byte in the skip table
  for(i=0; i<skip_size ; i++) {
    bits=0;
    for(j=0; j<8 ; j++) {
      // rotate through each skip bit in current byte
      bits=bits << 1;
      if(GetFatEntry('f',NULL,in,block) == 0) {
      // if Ensoniq FAT says empty block then set the current skip bit
	  // and do not write any extra data to the EDA/EDE image
	  bits=bits | 0x01;
      } else {
        // otherwise write the used block as normal
		lseek(in, block * BLOCK_SIZE, SEEK_SET);
		read(in,Data, BLOCK_SIZE);
		write(out,Data,BLOCK_SIZE);
      }
      block++;
    }
    SkipTable[i]=bits;
  }
  // Write last EOF-marker
  //fputc(0x1A,out);
  Data[0]=0x1A;
  write(out,Data,1);

  lseek(out, skip_start, SEEK_SET);
  write(out,SkipTable,skip_size);
  return(OK);
}


///////////////
// IsEFE
//------
// Checks if file extension is proper for Giebler EFE/EFA or INS.
// Also checks presence of expected signature bytes for validity.
//
int IsEFE(int *in, char in_file[FILENAME_MAX])
{
  char *p;								// holds file extension
  char sig_chk_tmp;						// holds one EFE byte at a time while checking signatures

  // Check if file even has any extension at all.
  if((p=rindex(in_file,'.')) != NULL) {

    // Extension found!
    p++;
    //printf("Extension: %s\r\n",p);

	// Check that the file extension is one of the three supported types (EFE, EFA, or INS).
	if((strcasecmp(p,"efe") == 0) || (strcasecmp(p,"efa") == 0) || (strcasecmp(p,"ins") == 0)) {
		// file is already open, so start reading signatures
		// Byte offset $00 & $01 and $2F & $30 must be 0x0D & 0x0A.
		// Byte offset $31 must be 0x1A.
		lseek(*in, 0, SEEK_SET);
		read(*in,&sig_chk_tmp,1);
		if(sig_chk_tmp != 0x0D) return(ERR);
		lseek(*in, 1, SEEK_SET);
		read(*in,&sig_chk_tmp,1);
		if(sig_chk_tmp != 0x0A) return(ERR);
		lseek(*in, 47, SEEK_SET);
		read(*in,&sig_chk_tmp,1);
		if(sig_chk_tmp != 0x0D) return(ERR);
		lseek(*in, 48, SEEK_SET);
		read(*in,&sig_chk_tmp,1);
		if(sig_chk_tmp != 0x0A) return(ERR);
		lseek(*in, 49, SEEK_SET);
		read(*in,&sig_chk_tmp,1);
		if(sig_chk_tmp != 0x1A) return(ERR);
		// since extension matches and all signatures are good...
		return(OK);
    } // end of extension checking
	// otherwise file has the wrong extension, so assume not Ensoniq and fall-through to error
  } // end of if-not-null

  // When input file has wrong or missing extension, can't be opened, or is
  // missing any signatures then generate an error.
  return(ERR);
}


///////////////////
// GetImageType
// ------------
// Mostly assumes a GKH, EDE, or EDA is actually the type of file
// that the file extension declares it to be. However, some sanity
// checks for raw IMG could be added such as "ID" string at 0x226
// or "OS" at 0x41C, etc.
int GetImageType(char in_file[FILENAME_MAX], char *image_type)
{
  char *p;
  struct stat stat_buf;

  if((p=rindex(in_file,'.')) != NULL) {

    // Extension found!
    p++;
    //printf("Extension: %s\r\n",p);

    if(strcasecmp(p,"gkh") == 0) {
      //printf("GKH file found\r\n");
      *image_type=GKH_TYPE;
      return(OK);
    } else if(strcasecmp(p,"ede") == 0) {
      //printf("EDE file found\r\n");
      *image_type=EDE_TYPE;
      return(OK);
    } else if(strcasecmp(p,"eda") == 0) {
      //printf("EDA file found\r\n");
      *image_type=EDA_TYPE;
      return(OK);
    }
  }

  // No or unknown extension - check if known raw-image


  // Uncomment for header-check when raw-image expected
  /*
    if((in=fopen(in_file, "rb"))== NULL) {
    EEXIT((stderr, "ERROR: Couldn't open file '%s'.", in_file));

    }

    fseek(in, 512,0);
    fread(&Hdr,sizeof(unsigned long), 1,in);

    printf("hdr: %lx \r\n", Hdr);
  */

  if(stat(in_file,&stat_buf) != 0) {
    //fprintf(stderr,"\r\n(line: %d) ERROR: Can't get the filesize!!\r\n", __LINE__);
    return(ERR);
  }

  //printf("filesize: %ld\r\n",stat_buf.st_size);

  if(stat_buf.st_size == EPS_IMAGE_SIZE) {
    //printf("EPS file found\r\n");
    *image_type = EPS_TYPE;
    return(OK);
  } else if(stat_buf.st_size == ASR_IMAGE_SIZE) {
    //printf("ASR file found\r\n");
    *image_type = ASR_TYPE;
    return(OK);
  } else if(stat_buf.st_size == E16_SD_IMAGE_SIZE) {
    //printf("EPS16 SuperDisk file found\r\n");
    *image_type = E16_SD_TYPE;
    return(OK);
  } else if(stat_buf.st_size == ASR_SD_IMAGE_SIZE) {
    //printf("ASR SuperDisk file found\r\n");
    *image_type = ASR_SD_TYPE;
    return(OK);
  } else {
    //fprintf(stderr,"\r\nWarning! Not a known file format. Might be an HDD image or SCSI device!  \r\n\r\n");
    *image_type = OTHER_TYPE;
    return(OK);
  }

}

////////////////////
// GetTHS
//-------
// Calculates Track, Head, and Sector location for any given block.
void GetTHS(unsigned int block, unsigned int num_of_sect,
	    unsigned int *track, unsigned int *head, unsigned int *sector)
{
  *track  = block / (2 * num_of_sect);
  *head   = (block - (*track * 2 * num_of_sect))  / num_of_sect;
  *sector = block - (*track * 2 * num_of_sect) - (*head * num_of_sect);
}


////////////////////
// OpenFloppy
FD_HANDLE OpenFloppy (int drive)
{
  FD_HANDLE fd;

#ifdef __CYGWIN__
  DWORD dwRet;
  char szDevice[32];
  DWORD dwVersion = 0;

  HANDLE h = CreateFile("\\\\.\\fdrawcmd", GENERIC_READ|GENERIC_WRITE, 0, NULL, OPEN_EXISTING, 0, NULL);

  if (h != INVALID_HANDLE_VALUE)
    {
      DeviceIoControl(h, IOCTL_FDRAWCMD_GET_VERSION, NULL, 0, &dwVersion, sizeof(dwVersion), &dwRet, NULL);
      CloseHandle(h);
    } else {
      printf("fdrawcmd.sys is not installed, see: http://simonowen.com/fdrawcmd/ \r\n");
      exit(ERR);
    }

    if (HIWORD(dwVersion) != HIWORD(FDRAWCMD_VERSION)) {
      printf("The installed fdrawcmd.sys is not compatible with this utility. \r\n");
      exit(ERR);
    }

    wsprintf(szDevice, "\\\\.\\fdraw%u", drive);

    if( (fd = CreateFile(szDevice, GENERIC_READ|GENERIC_WRITE, 0, NULL, OPEN_EXISTING, 0, NULL)) ==  INVALID_HANDLE_VALUE) {
      printf("OpenFloppy - CreateFile: (%ld) %s\r\n",GetLastError (), LastError());
      exit(ERR);
    }

    if(DeviceIoControl(fd, IOCTL_FD_RESET, NULL, 0, NULL, 0, &dwRet, NULL) == 0) {
      printf("OpenFloppy - RESET: (%ld) %s\r\n",GetLastError (), LastError());
      exit(ERR);
    }

#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  fd = open( "/dev/fd0", O_ACCMODE | O_NDELAY);
  //fd = open( "/dev/fd0", O_ACCMODE | O_SYNC);
  if ( fd < 0 ){
    perror("open floppy");
    exit(ERR);
  }
#endif
  return fd;
}

////////////////////
// CloseFloppy
void CloseFloppy(FD_HANDLE fd)
{
#ifdef __CYGWIN__
  CloseHandle(fd);
#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  close(fd);
#endif
}

//////////////////////////////////////
// Set FD geometry. 'a'=ASR, 'e'=EPS
void FD_SetGeometry(FD_HANDLE fd, char disk_type)
{
#ifdef __CYGWIN__
  DWORD dwRet;
  BYTE DataRate;

  if(disk_type == 'a') {
    // ASR (hd-disk)
    DataRate=0;
  } else {
    // EPS (dd-disk)
    DataRate=2;
  }

  if (DeviceIoControl(fd, IOCTL_FD_SET_DATA_RATE, &DataRate, sizeof(DataRate), NULL, 0, &dwRet, NULL) ==0) {
    printf("FD_SetGeometry - SET_DATA_RATE: (%ld) %s\r\n",GetLastError (), LastError());
    exit(ERR);
  }

#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  struct floppy_struct g;

  if(disk_type == 'a') {
    // Geometry of ASR-Disk
    g.size = 3200;
    g.sect = 20;

  } else {
    // Geometry of EPS-Disk
    g.size = 1600;
    g.sect = 10;
  }

  // Common parameters
  g.head = 2;
  g.track = 80;
  g.stretch = 0;

  // Set Disk geometry
  if(ioctl(fd, FDSETPRM , &g) < 0) {
    perror("geometry ioctl");
    exit(ERR);
  }
#endif
}

// Calibrate FD
void FD_Calibrate(int fd)
{

#ifdef __CYGWIN__
  // do nothing
#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  struct floppy_raw_cmd raw_cmd;

  // Calibrate
  raw_cmd.flags     = 8;
  raw_cmd.cmd_count = 2;
  raw_cmd.cmd[0]    = 7;
  raw_cmd.cmd[1]    = 0;

  if (ioctl( fd, FDRAWCMD, & raw_cmd) < 0 ){
    perror("raw cmd");
    exit(ERR);
  }
#endif
}

///////////////////////
// Seek the FD track
void FD_Seek(FD_HANDLE fd, int track)
{

#ifdef __CYGWIN__
  DWORD dwRet;
  FD_SEEK_PARAMS sp;

  // details of seek location
  sp.cyl = track;
  sp.head = 0;

  // seek
  if(DeviceIoControl(fd, IOCTL_FDCMD_SEEK, &sp, sizeof(sp), NULL, 0, &dwRet, NULL)==0) {
    printf("FD_Seek - SEEK: (%ld) %s\r\n",GetLastError (), LastError());
    exit(ERR);
  }

#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  struct floppy_raw_cmd raw_cmd;

  // SEEK
  raw_cmd.flags     = 8;
  raw_cmd.cmd_count = 3;
  raw_cmd.cmd[0]    = 15;
  raw_cmd.cmd[1]    = 0;
  raw_cmd.cmd[2]    = track;

  if (ioctl( fd, FDRAWCMD, & raw_cmd ) < 0 ){
    perror("raw cmd");
    exit(ERR);
  }
#endif
}

////////////////////////////
// FD_Raw Read/Write Track
// (read: rw=1, write: rw=2)
int FD_RawRW_DiskTrack(FD_HANDLE fd, char disk_type, int track, int head, char *buffer, int rw)
{
#ifdef __CYGWIN__
  unsigned int datalen;
  DWORD dwRet;
  FD_READ_WRITE_PARAMS rwp;
  FD_SEEK_PARAMS sp;

  rwp.flags = FD_OPTION_MFM;
  rwp.phead = head;
  rwp.cyl = track;
  rwp.head = head;
  rwp.sector = 0;
  rwp.size = 2;
  rwp.gap = 0x0a;
  rwp.datalen = 0xff;

  // Seek
  sp.cyl = track;
  sp.head = head;

  if(disk_type == 'a') {
    // ASR (hd-disk)
    rwp.eot = 20;
    datalen= 20*512;
    FD_SetGeometry(fd, 'a');

  } else {
    // EPS (dd-disk)
    rwp.eot = 10;
    datalen= 10*512;
    FD_SetGeometry(fd, 'e');
  }

  if(DeviceIoControl(fd, IOCTL_FDCMD_SEEK, &sp, sizeof(sp), NULL, track, &dwRet, NULL) ==0) {
    printf("FD_RawRW_DiskTrack - SEEK: (%ld) %s\r\n",GetLastError(), LastError());
    exit(ERR);
  }

  if(rw==1) {
    // READ TRACK
    if(DeviceIoControl(fd, IOCTL_FDCMD_READ_DATA, &rwp, sizeof(rwp), buffer, datalen, &dwRet, NULL)==0) {
      //printf("FD_RawRW_DiskTrack - READ_DATA: (%ld) %s\r\n",GetLastError (), LastError());
      //exit(ERR);
      return(ERR);
    }

  } else {
    // WRITE TRACK
    if(DeviceIoControl(fd, IOCTL_FDCMD_WRITE_DATA, &rwp, sizeof(rwp), buffer, datalen, &dwRet, NULL)==0) {
      printf("FD_RawRW_DiskTrack - WRITE_DATA: (%ld) %s\r\n",GetLastError (), LastError());
      exit(ERR);
    }
  } // end else

#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  struct floppy_raw_cmd raw_cmd;

  // RAW-COMMANDS

  if(disk_type == 'a') {
    //ASR
    raw_cmd.length    = 512*20;
    raw_cmd.rate      = 0;
    raw_cmd.flags     = 136+rw; // read=137, write=138
    raw_cmd.cmd[6]    = 20;    // Sectors (20)
  } else {
    //EPS
    raw_cmd.length    = 512*10;
    raw_cmd.rate      = 2;
    raw_cmd.flags     = 136+rw;  // read=137, write=138
    raw_cmd.cmd[6]    = 10;     // Sectors (10)
  }

  // Common parameters
  raw_cmd.data      = buffer;
  raw_cmd.track     = track;
  raw_cmd.cmd_count = 9;

  raw_cmd.cmd[0]    = 230-33*(rw-1); // read=230, write=197
  raw_cmd.cmd[1]    = head*4;
  raw_cmd.cmd[2]    = track;
  raw_cmd.cmd[3]    = head;
  raw_cmd.cmd[4]    = 0;
  raw_cmd.cmd[5]    = 2;
  raw_cmd.cmd[7]    = 27;
  raw_cmd.cmd[8]    = 255;

  if (ioctl( fd, FDRAWCMD, & raw_cmd) < 0 ){
    //perror("Disk access");
    EEXIT((stderr,"\r\nPlease insert Ensoniq disk in disk drive or define an image file!\r\n\r\n"));
  }

  if (raw_cmd.reply[0]>= 40) {
    return(ERR);
  }

#endif
  return(OK);
}

////////////////////////////
// FD_Raw Read/Write Blocks
// (read: rw=1, write: rw=2)
int FD_RawRW_DiskSectors(FD_HANDLE fd, char disk_type, int track, int head,
			 int sector, int num_of_sectors, char *buffer, int rw)
{

#ifdef __CYGWIN__
  unsigned int datalen;
  DWORD dwRet;
  FD_READ_WRITE_PARAMS rwp;
  FD_SEEK_PARAMS sp;

  rwp.flags = FD_OPTION_MFM;
  rwp.phead = head;
  rwp.cyl = track;
  rwp.head = head;
  rwp.sector = sector;
  rwp.size = 2;
  rwp.gap = 0x0a;
  rwp.datalen = 0xff;

  // Seek
  sp.cyl = track;
  sp.head = head;

  rwp.eot = sector+num_of_sectors;
  datalen= num_of_sectors*512;

  if(DeviceIoControl(fd, IOCTL_FDCMD_SEEK, &sp, sizeof(sp), NULL, track, &dwRet, NULL) ==0) {
    printf("FD_RawRW_DiskTrack - SEEK: (%ld) %s\r\n",GetLastError(), LastError());
    exit(ERR);
  }

  if(rw==1) {
    // READ BLOCKS
    if(DeviceIoControl(fd, IOCTL_FDCMD_READ_DATA, &rwp, sizeof(rwp), buffer, datalen, &dwRet, NULL)==0) {
      printf("FD_RawRW_DiskSectors - READ_DATA: (%ld) %s\r\n",GetLastError (), LastError());
      exit(ERR);
    }

  } else {
    // WRITE BLOCKS
    if(DeviceIoControl(fd, IOCTL_FDCMD_WRITE_DATA, &rwp, sizeof(rwp), buffer, datalen, &dwRet, NULL)==0) {
      printf("FD_RawRW_DiskSectors - WRITE_DATA: (%ld) %s\r\n",GetLastError (), LastError());
      exit(ERR);
    }
  } // end else

#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  struct floppy_raw_cmd raw_cmd;

  // RAW-COMMANDS

  if(disk_type == 'a') {
    //ASR
    raw_cmd.length    = 512*num_of_sectors;
    raw_cmd.rate      = 0;
    raw_cmd.flags     = 136+rw;
    raw_cmd.cmd[6]    = 20; // Sectors (20)
  } else {
    //EPS
    raw_cmd.length    = 512*num_of_sectors;
    raw_cmd.rate      = 2;
    raw_cmd.flags     = 136+rw;
    raw_cmd.cmd[6]    = 10; // Sectors (10)
  }

  // Common parameters
  raw_cmd.data      = buffer;
  raw_cmd.track     = track;
  raw_cmd.cmd_count = 9;

  raw_cmd.cmd[0]    = 230-33*(rw-1); // read=230, write=197
  raw_cmd.cmd[1]    = head*4;
  raw_cmd.cmd[2]    = track;
  raw_cmd.cmd[3]    = head;
  raw_cmd.cmd[4]    = sector;
  raw_cmd.cmd[5]    = 2;
  raw_cmd.cmd[7]    = 27;
  raw_cmd.cmd[8]    = 255;

  if (ioctl( fd, FDRAWCMD, & raw_cmd) < 0 ){
    //perror("Disk access");
    EEXIT((stderr,"\r\nPlease insert Ensoniq disk in disk drive or define image file! \r\n\r\n"));
  }

  if (raw_cmd.reply[0]>= 40) {
    return(ERR);
  }

#endif
  return(OK);
}

#ifdef __CYGWIN__
  // do nothing
#elif __APPLE__
  // macOS, so do nothing
#else // Linux
// Datatypes for Format
typedef struct {
  char track;
  char head;
  char sector;
  char szcode;
} FormatHeader;

typedef FormatHeader FormatHeaders[MAX_DISK_SECT];
#endif


////////////////////
// Format DiskTrack
int FD_Format_DiskTrack(FD_HANDLE fd, int track, int head, int nsect, int rate, int skew)
{

#ifdef __CYGWIN__
  DWORD dwRet;
  BYTE abFormat[sizeof(FD_FORMAT_PARAMS) + sizeof(FD_ID_HEADER)*20];

  BYTE s;
  PFD_FORMAT_PARAMS pfp = (PFD_FORMAT_PARAMS)abFormat;
  PFD_ID_HEADER ph = pfp->Header;
  pfp->flags = FD_OPTION_MFM;
  pfp->phead = head;
  pfp->size = 2;
  pfp->sectors = nsect;
  pfp->gap = 0x20;
  pfp->fill = 0x00;

  for ( s = 0 ; s < (pfp->sectors) ; s++,ph++)
    {
      ph->cyl = track;
      ph->head = head;
      ph->sector = (s+skew) % nsect;
      ph->size = pfp->size;
    }

  if(DeviceIoControl(fd, IOCTL_FDCMD_SEEK, &track, sizeof(track), NULL, track, &dwRet, NULL) ==0) {
    printf("FD_RawRW_DiskTrack - SEEK: (%ld) %s\r\n",GetLastError(), LastError());
    exit(ERR);
  }

  if(DeviceIoControl(fd, IOCTL_FDCMD_FORMAT_TRACK, pfp,(ULONG) ((PBYTE)ph - abFormat), NULL, 0, &dwRet, NULL)==0) {
    printf("FD_Format_DiskTrack - FORMAT_TRACK: (%ld) %s\r\n",GetLastError(), LastError());
    exit(ERR);
  }

#elif __APPLE__
  // macOS, so do nothing
#else // Linux
  FormatHeaders headers;
  struct floppy_raw_cmd raw_cmd;
  int i,tmp;

  for (i=0; i<nsect; i++)
    {

      headers[i].track    = track;                  // track
      headers[i].head     = head;                   // head
      headers[i].sector   = (i+skew) % nsect;       // sector (with skew ie. sector shift)
      headers[i].szcode   = 2;                      // sizecode
    }

  raw_cmd.track     = track;
  raw_cmd.data      = headers;
  raw_cmd.length    = 4*nsect;
  raw_cmd.rate      = rate;
  raw_cmd.flags     = 138;
  raw_cmd.cmd_count = 6;
  raw_cmd.cmd[0]    = 77;
  raw_cmd.cmd[1]    = head*4;
  raw_cmd.cmd[2]    = 2;
  raw_cmd.cmd[3]    = nsect;
  raw_cmd.cmd[4]    = 40;
  raw_cmd.cmd[5]    = 0;

  tmp = ioctl( fd, FDRAWCMD, & raw_cmd );
  if ( tmp < 0 ){
    perror("raw cmd");
    exit(ERR);
  }

  if (raw_cmd.reply[0]>= 40) {
    //printf("\r\nERROR at: head=%d, track=%d !!\r\n\r\n",head,track);
    printf("\r\n\r\nDisk is WRITE PROTECTED!! \r\n\r\n");
    return(ERR);
  }

#endif
  return(OK);
}

////////////////
// MakeID_Block
void MakeID_Block(unsigned char *buffer, char *label, unsigned int tracks,
		  unsigned int nsect, unsigned int total_blks)
{
  int i;

   // initialize an empty block
  for(i=0; i<BLOCK_SIZE;i++) {
    buffer[i]=0;
  }

  // Device type -- redundant because already zero, but...
  buffer[0] = 0x00;

  // Removable Media device Type
  buffer[1] = 0x80;

  // Std. Version #
  buffer[2] = 0x01;

  // SCSI -- redundant because already zero, but...
  buffer[3] = 0x00;

  // Nsect
  buffer[4] = 0x00;  buffer[5] = (unsigned char) nsect;

  // Heads
  buffer[6] = 0x00;  buffer[7] = 0x02;

  // Tracks
  buffer[8] = 0x00;  buffer[9] = (unsigned char) tracks;

  // Bytes per Block - 512
  buffer[10] = 0x00;  buffer[11] = 0x00;  buffer[12] = 0x02;  buffer[13] = 0x00;

  // Total Blocks

  buffer[14] = (total_blks >> 24) & 0x000000ff; // MSB
  buffer[15] = (total_blks >> 16) & 0x000000ff;
  buffer[16] = (total_blks >>  8) & 0x000000ff;
  buffer[17] =  total_blks        & 0x000000ff; // LSB

  // SCSI Medium Type
  buffer[18] = 0x1e;

  // SCSI Density Code
  buffer[19] = 0x02;

  // reserved (20-29)

  // Disk label is always seven characters.
  if(label != NULL) {
	// an 0xFF always comes before the disk label
	buffer[30] =  0xff;
    for(i=0;i<DISK_LABEL_SIZE;i++) {
      buffer[31+i] = label[i];
    }
  }

  // Write "ID" signature directly after disk label.
  buffer[38] = 'I';  buffer[39] = 'D';

}

/////////////////
// MakeOS_Block
void MakeOS_Block(unsigned char *buffer, unsigned int free_blks)
{
  int i;

  // initialize an empty block
  for(i=0; i<BLOCK_SIZE;i++) {
    buffer[i]=0;
  }

  // First four bytes of the OS block hold the amount of free
  // blocks in the entire disk -- 32-bit big endian.
  buffer[0] = (free_blks >> 24) & 0x000000ff; // MSB
  buffer[1] = (free_blks >> 16) & 0x000000ff;
  buffer[2] = (free_blks >>  8) & 0x000000ff;
  buffer[3] =  free_blks        & 0x000000ff; // LSB

  // Write "OS" signature at proper location in block.
  buffer[28] = 'O';
  buffer[29] = 'S';
}

/////////////////
// MakeDR_Block
void MakeDR_Block(unsigned char *buffer, int write_id)
{
  int i;

  // initialize an empty block
  for(i=0; i<BLOCK_SIZE;i++) {
    buffer[i]=0;
  }

  // write "DR" signature as last two bytes of block...
  // ...but only for second directory block!
  if(write_id == 1) {
    buffer[510]='D';
    buffer[511]='R';
  }

}


//////////////////////
// Format Disk
// -----------
// This performs format on a physical disk in an internal floppy drive only!

void FD_Format_Disk(char disk_type, int nsect, int rate, char* disk_label)
{

  FD_HANDLE fd;
  int track,head,free_blks,fat_blks,i,j,skew,head_skew,track_skew;
  unsigned char buffer[BLOCK_SIZE*40];
  char str[81],tmp;

  // Initialize the skew factor for the disk.
  if(disk_type=='e') {

    track_skew = nsect-2;
    head_skew  = nsect-1;
    skew       = -track_skew;

  } else {

    track_skew = nsect-3;
    head_skew  = nsect-2;
    skew       = -track_skew;

  }

  // Calculate disk parameters.
  // This can remain hardcoded as physical disks will never vary.
  fat_blks  = nsect*2*80 / FAT_ENTRIES_PER_BLK +1;
  free_blks = nsect*2*80 - (5 + fat_blks);

  //Open FD
  fd = OpenFloppy(0);

  FD_SetGeometry(fd,disk_type);

  printf("1       10        20        30        40        50        60        70        80\r\n");
  sprintf(str,"|---+----|----+----|----+----|----+----|----+----|----+----|----+----|----+----|");

  for(track=0; track<80; track++) {

    // Shift sectors (track skew)
    skew=skew+track_skew;

    for(head=0; head<2; head++) {

      if(head==0) {
	tmp = str[track];

	str[track]='\\';

      } else {
	// Shift sectors (head skew)
	skew=skew+head_skew;

	str[track]='/';

      }
      printf("\r%s",str);
      fflush(stdout);

      if((FD_Format_DiskTrack(fd,track,head,nsect,rate,skew)) == ERR) {
        exit(ERR);
      }
    } //for head
    if(tmp == '|') str[track]=tmp; else str[track]='#';
  }// for track

  printf("\r%s",str);
  fflush(stdout);
  printf("\r\n\r\nWriting System blocks... \r\n");

  // TODO: Get the FD status so we don't have to wait

  sleep(1);

  // Write System blocks

  for(i=0; i<BLOCK_SIZE*40;i++) {
    buffer[i]=0;
  }

  // ID-Block
  MakeID_Block(buffer+BLOCK_SIZE,disk_label,80,nsect,2*80*nsect);

  // OS-Block
  MakeOS_Block(buffer+BLOCK_SIZE*2, free_blks);

  // Write Dir-ID (to second Dir-Block)
  buffer[BLOCK_SIZE*4 + 510] = 'D';
  buffer[BLOCK_SIZE*4 + 511] = 'R';

  // FAT blocks
  for(i=0; i<fat_blks; i++) {
	// handle first FAT block only
	if(i==0) {
      for(j=0; j<(fat_blks+5); j++) {
		// write "001" code for all blocks used by block 0, ID, OS, DR, and FAT
		buffer[BLOCK_SIZE * 5  +  3*j  + 2] = 1;
      }
    }
	// write "FB" code at end of each FAT block
    buffer[BLOCK_SIZE * (5+i) + 510] = 'F';
    buffer[BLOCK_SIZE * (5+i) + 511] = 'B';
  }

  if(FD_RawRW_DiskTrack(fd,disk_type,0,0,buffer,WRITE) == ERR) {
    EEXIT((stderr,"ERROR: Couldn't write System data to disk!! \r\n\r\n"));
  }

  if(FD_RawRW_DiskTrack(fd,disk_type,0,1,buffer+(nsect*BLOCK_SIZE),WRITE) == ERR) {
    EEXIT((stderr,"ERROR: Couldn't write System data to disk!! \r\n\r\n"));
  }

  printf("Operation completed successfully! \r\n\r\n");

  CloseFloppy(fd);
}

///////////////////////////////////////////////////////////
// Check which type of disk is inserted (EPS=DD or ASR=HD)
int FD_GetDiskType(char *disk_type, unsigned int *nsect, unsigned int *trk_size)
{

  FD_HANDLE fd;
  char buffer[20*512];

  *disk_type='n';

  //Open FD
  fd=OpenFloppy(0);

  // EPS-Disk !? (DD)
  FD_SetGeometry(fd,'e');
  if((FD_RawRW_DiskTrack(fd,'e',0,0,buffer,READ) )== ERR) {

    //.. OR ASR-Disk !? (HD)
    FD_SetGeometry(fd,'a');
    if((FD_RawRW_DiskTrack(fd,'a',0,0,buffer,READ) )== ERR) {

      // NEITHER :(
      return(ERR);

    } else { // ASR
      //printf("\r\nASR disk detected..\r\n");
      *disk_type = 'a';
      *nsect=20;
      *trk_size = 20* 512;
    }
  } else { // EPS
    //printf("\r\nEPS disk detected..\r\n");
    *disk_type = 'e';
    *nsect=10;
    *trk_size = 10* 512;
  }

  CloseFloppy(fd);

  return(OK);
}

//////////////////////////
// Read/Write the Disk
void FD_RW_Disk(char in_file[FILENAME_MAX], int rw_disk)
{
  int file;

  FD_HANDLE fd;
  int convert, idx, errors;
  unsigned int track, head, nsect, trk_size;
  char disk_type, image_type;
  char buffer[512 * 20],str[81],tmp, filename[FILENAME_MAX];
  char mark[5] = {'\\','/','#','E','E'};
  char errors_text[20000];

  errors=0; idx=0; errors_text[0]='\0';

  // Check image file
  if((GetImageType(in_file, &image_type) ==  ERR) && (rw_disk == WRITE)) {
    EEXIT((stderr,"ERROR: Not a valid image! \r\n\r\n"));
  }

  // Check disk
  if(FD_GetDiskType(&disk_type, &nsect, &trk_size) == ERR) {
    EEXIT((stderr,"ERROR: Not an Ensoniq Disk. \r\n\r\n"));
  }

  // Check if disk and file types match
  if(disk_type == EPS_TYPE) {
    strcpy(str,"EPS DISK");
    if(image_type == EDA_TYPE) {
      EEXIT((stderr,"ERROR: Don't use EPS disks with EDA files! EPS requires 'ede' extension. \r\n"));
    }

  } else {
    strcpy(str,"ASR DISK");

    if(image_type == EDE_TYPE) {
      EEXIT((stderr,"ERROR: Don't use ASR disks with EDE files! ASR requires 'eda' extension. \r\n"));
    }
  }

  //Open FD
  fd=OpenFloppy(0);
  FD_SetGeometry(fd,disk_type);

  // If file type is other than image, conversion is needed

  if((image_type == GKH_TYPE) && (rw_disk == READ)) {
    EEXIT((stderr,"Sorry! Reading disk to GKH file is not yet supported! \r\n"));
  }

  if((image_type == EDE_TYPE) || (image_type == EDA_TYPE) || (image_type == GKH_TYPE)) {
    // Generate tmp-file and bind the clean-up for it
    //tmpnam(tmp_file);
    if(mkstemp(tmp_file) == -1) {
      perror("mkstemp");
      exit(ERR);
    }

    atexit(CleanTmpFile);
    convert = 1;
  } else {
    convert = 0;
    strcpy(filename,in_file);
  }

  // Open image-file
  if(rw_disk == READ) {
    if(convert) strcpy(filename,tmp_file);
    if((file = open(filename,O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",filename));
    }
    printf("Reading %s to file '%s'... \r\n\r\n",str,in_file);
  } else {

    // Check if conversion is needed
    if(convert) {

      if(ConvertToImage(in_file,tmp_file) == OK) {
	//printf("CONVERSION DONE!!!\r\n");
	//replace in_file to converted image
	strcpy(filename,tmp_file);
      } else {
	EEXIT((stderr,"ERROR: Something is wrong with the image file! \r\n"));

      }
    }

    file = open(filename,O_RDONLY | O_BINARY);
    printf("Writing %s from file '%s'... \r\n\r\n",str,in_file);
  }

  printf("1       10        20        30        40        50        60        70        80\r\n");
  sprintf(str,"|---+----|----+----|----+----|----+----|----+----|----+----|----+----|----+----|");

  for(track=0; track<80; track++) {
    //FD_Seek(fd,track);
    for(head=0; head<2; head++) {

      tmp = str[track];
      str[track]=mark[idx];

      printf("\r%s",str);
      fflush(stdout);

      if(rw_disk == WRITE)  {
		read(file,buffer,trk_size);
      }

      {
	  int retry_cnt=0;

      retry:

	if(FD_RawRW_DiskTrack(fd,disk_type,track,head,buffer,rw_disk) == ERR) {
	  // Error: 'E'
	  idx=2;
	  //Show retry count
	  str[track]='0'+retry_cnt;
	  printf("\r%s",str);
	  fflush(stdout);
	  retry_cnt++;
	  if (retry_cnt <= 9 ) goto retry; // Yes, I know.. The Goto is a "bad programming"

	  //Error text & count
	  sprintf(errors_text+strlen(errors_text),"  ERROR: track=%d, head=%d\r\n",track,head);
	  errors++;
	}

      }

      if(rw_disk == READ) {
		write(file,buffer,trk_size);
      }
      idx++;
    } //for head

    if((mark[idx] != 'E') && ((((track+1) % 10) == 0) || (track == 0))) str[track]='|';
    else str[track]=mark[idx];
    idx=0;
  }// for track

  printf("\r%s",str);
  fflush(stdout);

  if(convert && rw_disk==READ) {
    ConvertFromImage(filename,in_file,image_type);
  }

  if(errors > 0) {
    printf("\r\n\r\nWarning: %d error(s) found! \r\n",errors);
    printf("\r\n%s\r\n",errors_text);
  } else {
    printf("\r\n\r\nOperation completed successfully! \r\n\r\n");
  }

  CloseFloppy(fd);
}

/////////////////////////////////////////////////////////////////
// ReadBlocks
// ----------
//   media_type  :  'file'-access('f') or disk-access('e','a')
//   fd          :  device (dev/fd0) file descriptor (depends on media_type if needed!)
//   file        :  file descriptor (depends on media_type if needed!)
//   start_block :  First block to read
//   length      :  How many blocks to read
//   buffer      :  Where to put the data

int ReadBlocks(char media_type, FD_HANDLE fd, int file, unsigned int start_block,
	       unsigned int length, unsigned char *buffer)
{
  unsigned int sector,head,track;
  unsigned int end_sector,  end_head,  end_track;
  unsigned int end_block, cur_block,nsect = 0;
  // read buffer has a size of 20 blocks?
  unsigned char tmp_buffer[BLOCK_SIZE*20];
#ifdef __CYGWIN__
  unsigned int i,count,num_of_blocks;
  unsigned int pre_blocks;
  unsigned int post_blocks;
  unsigned int cont_blocks;
  unsigned int offset;
  int skip;

  //char tmp_buffer[2048];
#endif

  switch (media_type)
    {
    case 'f':
#ifdef __CYGWIN__
	case 's':

      num_of_blocks=length;

      // Calc how many blocks to read in PRE_LOAD state
      pre_blocks= (4-(start_block%4))%4;
      // Not all blocks in the end of PRE_BLOCKS needed
      // when only 1 or 2 blocks are read in the 2nd or 3rd
      // block of the 2048..

      skip=pre_blocks-num_of_blocks;
      if(skip > 0)
		pre_blocks=pre_blocks-skip;

      cont_blocks=((num_of_blocks-pre_blocks)/4)*4;
      post_blocks=(num_of_blocks-pre_blocks)%4;
      offset=(start_block*512) % 2048;

#ifdef DEBUG
	printf("Start_block=%d \r\n",start_block);
	printf("SEEK: %d - Offset=%d \r\n",(start_block/ 4)*2048,offset);

	printf("Pre_blocks=%d \r\n",pre_blocks);
	printf("Cont_blocks=%d \r\n",cont_blocks);
	printf("Post_blocks=%d \r\n",post_blocks);
	printf("Num_of_blocks=%d <-> total_blocks=%d \r\n",num_of_blocks,pre_blocks+cont_blocks+post_blocks);
#endif

      if( (lseek(file,(long) ((start_block / 4)*2048),SEEK_SET)) < 0) {
		perror("seek");
      }

      // PRE BLOCKS
      if(pre_blocks != 0) {
	//printf("PRE_LOAD  %d blocks\r\n",pre_blocks);

	if( read(file,tmp_buffer,2048) < 2048) {
	  printf("WARNING: Read error in PRE BLOCKS! \r\n");
	  printf("Resulting file is likely partially corrupt! \r\n");
	  // exit(ERR);
	}
	memcpy(buffer, tmp_buffer+offset,pre_blocks*512);
      }

      // CONT BLOCKS
      if( (cont_blocks != 0) && (skip<0)) {
	//printf("CONT_LOAD %d blocks\r\n",cont_blocks);
	if( read(file,buffer+(pre_blocks*512),512*cont_blocks) < (512*cont_blocks)) {
	  printf("WARNING: Read error in CONT BLOCKS! \r\n");
	  printf("Resulting file is likely partially corrupt! \r\n");
	  // exit(ERR);
	}

      }

      // POST BLOCKS
      if( (post_blocks != 0) && (skip<0)) {
	//printf("POST_LOAD %d blocks\r\n",post_blocks);
	if((read(file,buffer+(pre_blocks*512)+(cont_blocks*512),512*post_blocks)) < (512*post_blocks)) {
	  printf("WARNING: Read error in POST BLOCKS! \r\n");
	  printf("Resulting file is likely partially corrupt! \r\n");
	  // exit(ERR);
	}

      }

#else // Linux
    if(lseek(file, start_block * BLOCK_SIZE, SEEK_SET) == -1) {
		printf("ERROR in seek! \r\n");
		exit(ERR);
    }
    if(read(file,buffer, BLOCK_SIZE*length) == 0) {
		printf("ERROR in read! \r\n");
		exit(ERR);
    }
#endif
    return(OK);

    case 'e':

      nsect=10;
      break;

    case 'a':

      nsect=20;
      break;
    }
  GetTHS(start_block,nsect,&track,&head,&sector);

  end_block = start_block + length -1;

  GetTHS(end_block,nsect,&end_track,&end_head,&end_sector);

  FD_RawRW_DiskTrack(fd,media_type,track,head,tmp_buffer,READ);

  cur_block = start_block;

  while(cur_block <= end_block) {
    memcpy(buffer,tmp_buffer+(sector*BLOCK_SIZE), BLOCK_SIZE);

    buffer=buffer+BLOCK_SIZE;
    cur_block++;
    sector++;
    //printf("\r Reading from disk:  %-4d of %-4d (blocks) .. ", cur_block-start_block, end_block-start_block+1);
    //fflush(stdout);
    if(sector>(nsect-1) && cur_block <= end_block ) {
      //Load next track
      GetTHS(cur_block,nsect,&track,&head,&sector);
      FD_RawRW_DiskTrack(fd,media_type,track,head,tmp_buffer,READ);
      sector=0;
    }
  }
  //printf("\r                                                   ");
  //fflush(stdout);
  return(OK);

}

/////////////////////////////////////////////////////////////////
// WriteBlocks
// ----------
//   media_type  :  'file'-access('f') or disk-access('e','a')
//   fd          :  device (dev/fd0) file descriptor (depends on media_type if needed!)
//   file        :  file descriptor (depends on media_type if needed!)
//   start_block :  First block to write
//   length      :  How many blocks to write
//   buffer      :  Where to get the data

int WriteBlocks(char media_type, FD_HANDLE fd, int file, unsigned int start_block,
		unsigned int length, unsigned char *buffer)
{
  unsigned int sector, head, track;
  unsigned int end_sector, end_head, end_track;
  unsigned int end_block, cur_block,nsect = 0, num_of_sectors, start_sector, tmp;
  unsigned char tmp_buffer[BLOCK_SIZE*20];

  switch (media_type)
    {
    case 'f':
#ifdef __CYGWIN__
	case 's':
#endif
      lseek(file, start_block * BLOCK_SIZE, SEEK_SET);
      write(file,buffer, BLOCK_SIZE*length);
      return(OK);

    case 'e':
      nsect=10;
      break;

    case 'a':
      nsect=20;
      break;
    }

  GetTHS(start_block,nsect,&track,&head,&sector);
  end_block = start_block + length -1;
  GetTHS(end_block,nsect,&end_track,&end_head,&end_sector);

  cur_block = start_block;
  start_sector = sector;

  do {
    memcpy(tmp_buffer+(sector*BLOCK_SIZE),buffer, BLOCK_SIZE);
    buffer=buffer+BLOCK_SIZE;

    if(sector >= (nsect-1) || cur_block >= end_block ) {
      //Write blocks to disk

      num_of_sectors = sector - start_sector+1;
      GetTHS(cur_block,nsect,&track,&head,&tmp);

      FD_RawRW_DiskSectors(fd,media_type,track,head,start_sector, num_of_sectors, \
			   tmp_buffer+(start_sector*BLOCK_SIZE),WRITE);

      sector=0;
      start_sector=0;

    } else {
      sector++;
    }
    cur_block++;
    printf("\r Writing to disk: %-4d of %-4d (blocks)... ", cur_block-start_block, end_block-start_block+1);
    fflush(stdout);
  } while(cur_block <= end_block);
  printf("\r                                              ");
  fflush(stdout);
  return(OK);
}


//////////////////////////////////////////////
// Load Dir entry to EFE-array - use FAT-table
void LoadDirBlocks(char media_type, FD_HANDLE fd, unsigned char *DiskFAT, int file,
		   unsigned long start_blk, int cont, unsigned char EFE[][EFE_SIZE])
{

  unsigned char Dir[DIR_BLOCKS*BLOCK_SIZE];
  int i,j;

  // Get DirBlocks

  // First dir-block - Guess the block are contiguous, so read 2 blocks
  ReadBlocks(media_type,fd,file,start_blk,2,Dir);

  //.. and second, if needed (ie. not contiguous..)
  if(cont != 2) {
    ReadBlocks(media_type,fd,file,GetFatEntry(media_type,DiskFAT,file,start_blk),1,Dir+BLOCK_SIZE);
  }

  // Scan Directory
  for(i=0;i<MAX_NUM_OF_DIR_ENTRIES;i++) {
    for(j=0; j < EFE_SIZE ; j++) {
      EFE[i][j]=Dir[i * EFE_SIZE+j];
    }
  }
}

////////////////////////////////////////////////////
// FormatMedia
// -----------
// -Format (and create if needed) imagefile/device
//
int FormatMedia(char **argv, int argc, int optind, char format_arg, char *disk_label)
{
  int file;

  long long i,j,k,image_size, total_blks, free_blks, fat_blks,storage_overhead;
  long long partial_blks, rest_blks;
  unsigned char buffer[BLOCK_SIZE], nsect, tracks;

  image_size=0;

  switch(format_arg)
    {

    case 'a':
      // ASR Disk
      printf("\r\nFormatting ASR HD disk... \r\n\r\n");
      FD_Format_Disk('a',20,0,disk_label);
      return(OK);

      // EPS Disk
    case 'e':
      printf("\r\nFormatting EPS DD disk... \r\n\r\n");
      FD_Format_Disk('e',10,2,disk_label);
      return(OK);

    case 'i':

      // IMAGEFILE/DEVICE

      //Default  values for image/scsi (ie. "don't care")
      // Exception: for EPS/ASR _DISK_ images these values
      //            _has_ to be set correctly in the ID Block
      //            or else you have a disk that _instantly_
      //            reboots the keyboard when accessed!
      //            If You dare, test it yourself.. :-)
      nsect=0;
      tracks=0;

      // check if file argument exists
      if(argv[optind] == NULL) {
		ShowUsage();
		exit(ERR);
      }

	// Check if file already exists or not.
	if((file=open(argv[optind],O_RDWR | O_BINARY)) != -1) {

	// File already exists, so get its size...
	if((image_size=lseek(file,0,SEEK_END)) == -1) {
	  perror("lseek");
	  exit(ERR);
	}

	// Check if disk image size can even be valid for Ensoniq.
	if((image_size % BLOCK_SIZE) != 0) {
	  printf("Valid images must be a multiple of %d! \r\n",BLOCK_SIZE);
	  exit(ERR);
	}

	if(image_size == EPS_IMAGE_SIZE) {
	  // when image is 800K then assume it is EPS DD
	  tracks=80;
	  nsect=10;
	}
	if(image_size == ASR_IMAGE_SIZE) {
	  // when image is 1600K then assume it is ASR HD
	  tracks=80;
	  nsect=20;
	}
	if(image_size == E16_SD_IMAGE_SIZE) {
	  // when image is 2550K then assume EPS16 SuperDisk
	  tracks=255;
	  nsect=10;
	}
	if(image_size == ASR_SD_IMAGE_SIZE) {
	  // when image is 5110K then assume ASR SuperDisk
	  tracks=255;
	  nsect=20;
	}

	// Calculate amount of blocks since image_size is set in bytes.
	total_blks=image_size/BLOCK_SIZE;

      } else {

	// File does NOT already exist, so...

	// Check that file size was given as an argument.
	if(argv[optind+1] == NULL) {
	  printf("No file size was specified! \r\n\r\n");
	  exit(ERR);
	} else {

	  // Check specified size for template matches...
	  if((strcasecmp(argv[optind+1],"eps"))==0) {
        //eps disk image
	    // Set the correct values for nsect and tracks (see above)
	    tracks=80;
	    nsect=10;
	    image_size=EPS_IMAGE_SIZE;
	  } else if ((strcasecmp(argv[optind+1],"asr"))==0) {
	    //asr disk image
	    // Set the correct values for nsect and tracks (see above)
	    tracks=80;
	    nsect=20;
	    image_size=ASR_IMAGE_SIZE;
	  } else if ((strcasecmp(argv[optind+1],"e16sd"))==0) {
	    //EPS16 SuperDisk image
	    // Set the correct values for nsect and tracks (see above)
	    tracks=255;
	    nsect=10;
	    image_size=E16_SD_IMAGE_SIZE;
	  } else if ((strcasecmp(argv[optind+1],"asrsd"))==0) {
	    //ASR SuperDisk image
	    // Set the correct values for nsect and tracks (see above)
	    tracks=255;
	    nsect=20;
	    image_size=ASR_SD_IMAGE_SIZE;
	  // ...otherwise revert to generic numeric sizes
	  } else {
	    // specific size is taken from numeric command line argument
	    image_size=atol(argv[optind+1]);

	    if(image_size == 0) {
	      printf("Image size cannot be zero, obviously! \r\n\r\n");
	      exit(ERR);
	    } // end if

	    // Check if 'M' or 'K' suffix used
	    switch(argv[optind+1][strlen(argv[optind+1])-1])
	      {
			case 'm':
			case 'M':
			// express M value in actual bytes	-- ends up being 1024 squared because of...
			image_size=image_size*1024;         // ...fall-through to 'K' (no break statement)
			case 'k':
			case 'K':
			// express K value in actual bytes
			image_size=image_size*1024;
	      } // end switch
		} // end of numeric size command line routine
	} // end of new disk image sizing

	// Check the validity of the given filesize ie. that is multiple of block size

	if((image_size % BLOCK_SIZE) != 0) {
	  printf("Image size has to be a multiple of %d! \r\n",BLOCK_SIZE);
	  exit(ERR);
	}

	// Calculate amount of blocks since image_size is set in bytes.
	total_blks=image_size/BLOCK_SIZE;

	// create file
	file = open( argv[optind], O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS);

	// Make empty file
	// 1st clear the buffer
	for(k=0; k<BLOCK_SIZE;k++) {
	  buffer[k]=0;
	}

	// Divide progress into a percentage.
	partial_blks = total_blks/100;
	rest_blks    = total_blks % 100;

	// Write 100 percent of blocks, but one percent at a time.
	for(j=0;j<100;j++) {
	  printf("\rCreating image file... %d%% completed", (int) j);
	  fflush(stdout);
      // Write amount of blocks which correspond to one percent completion.
	  for(i=0; i< partial_blks;i++) {
	    write(file,buffer,BLOCK_SIZE);
	  }
	}
	// Write the few remaining blocks, if any.
	for(i=0;i<rest_blks;i++) {
	  write(file,buffer,BLOCK_SIZE);
	}
	printf("\rCreating image file...  OK!                     \r\n");
	fflush(stdout);
    }

      // Calculate number of needed FAT blocks.
      printf("\rWriting filesystem...");
      fflush(stdout);

		// Each FAT block holds only so many entries, so take total
		// amount of needed blocks and divide by 170 which is the
		// amount of entries which can be stored in one FAT block.
		//
		// Division result usually has to be adjusted up by one, except
		// when blocks needed is perfectly divisible by 170.
		//    ex: 800K = 1600 blocks, so 9.4 FAT blocks needed.
		//        Cannot have partial FAT blocks, so a full 10
		//        FAT blocks are required.
		//
		//        However, 850K = 1700 blocks, so exactly 10 FAT
		//        blocks are needed.
		//
		if((total_blks % FAT_ENTRIES_PER_BLK) != 0)
		{
			fat_blks=total_blks/FAT_ENTRIES_PER_BLK+1;
		} else {
			fat_blks=total_blks/FAT_ENTRIES_PER_BLK;
		}

      // There is always at least a 5 block overhead due to null block,
      // ID block, OS block, and two DR blocks. Then add all FAT blocks
      // to calculate total storage overhead.
      //
      // This is the amount of blocks which have to be marked in the FAT
      // as allocated, even though the "blank" disk has nothing stored
      // except formatting and disk geometry information.
      //
      storage_overhead=fat_blks+5;

	  // Calculate amount of empty blocks left after overhead.
      free_blks=total_blks-storage_overhead;

      //
      // Write null block (block 0) -- technically unused, so some programs
	  // put extra info here such as "Formatted by <xyz>", etc. but stock
	  // Ensoniq disks use a specific byte pattern as filler.
	  //
      lseek(file,0,SEEK_SET);
	  // Create buffer filled with traditional Ensoniq filler bytes.
	  for(i=0; i<BLOCK_SIZE;i=i+2) {
		buffer[i  ]=0x6D;
		buffer[i+1]=0xB6;
      }
      // Alternately, create an empty buffer with EpsLin message.
	  //for(i=0;i<BLOCK_SIZE;i++) buffer[i]=0;
      //sprintf(buffer,"m%s",FIRST_BLOCK_MESSAGE);
      write(file,buffer,BLOCK_SIZE);

      // Write ID block.
      lseek(file,BLOCK_SIZE*ID_BLOCK,SEEK_SET);
      MakeID_Block(buffer,disk_label,tracks,nsect,total_blks);
      write(file,buffer,BLOCK_SIZE);

      // Write OS block.
      lseek(file,BLOCK_SIZE*OS_BLOCK,SEEK_SET);
      MakeOS_Block(buffer,free_blks);
      write(file,buffer,BLOCK_SIZE);

      // Write first DR (directory) block.
      lseek(file,BLOCK_SIZE*DIR_START_BLOCK,SEEK_SET);
      MakeDR_Block(buffer,0);	// 0 argument means no "DR" signature
      write(file,buffer,BLOCK_SIZE);
      // Write second DR (directory) block.
      lseek(file,BLOCK_SIZE*DIR_END_BLOCK,SEEK_SET);
      MakeDR_Block(buffer,1);	// 1 argument means write "DR" signature
      write(file,buffer,BLOCK_SIZE);

      // Write all FAT blocks.

      // Buffer is already mostly empty from previous MakeDR, so just
	  // update the last two bytes with an "FB" signature.
      buffer[510] = 'F';		// "FB" is always the last two bytes...
      buffer[511] = 'B';		// ...of any FAT block

	  // Run loop once per FAT block being created.
      for(i=0; i<fat_blks; i++) {

		// Clear block buffer (except "FB" signature) every pass.
		for(k=0; k<BLOCK_SIZE-2;k++) {
			buffer[k]=0;
		}

		// Allocate FAT entries for all disk overhead blocks of:
		// Null block, ID block, OS block, two DR blocks, and all FAT blocks.
		//
		// Each FAT entry is three bytes, and "001" means block allocated.
		//
		if(storage_overhead > 0) {				// if any used blocks have still not been marked
			for(j=0; j<BLOCK_SIZE-2; j=j+3) {	// then mark as many entries as possible within the
				buffer[j]   = 0;				// current FAT block. Last two bytes must stay "FB"
				buffer[j+1] = 0;				// so never write to them.
				buffer[j+2] = 1;				//
				storage_overhead--;				// block now marked as used, so decrement count
				if(storage_overhead == 0) {
					break;						// no more entries to mark
				}
			} // end of used block marking loop
		}

        // Go to starting write position of current FAT entry.
		lseek(file,BLOCK_SIZE*(i+5),SEEK_SET);
		// Write current FAT block to disk.
		if( write(file,buffer,BLOCK_SIZE) <= 0)
			perror("write:");
      } // end of for loop done once per FAT

      printf("\rWriting filesystem....  OK! \r\n");
      fflush(stdout);
      close(file);
    } // case
  return(OK);
}

////////////////////////////////////////////////
// Save Dir entry from EFE-array - use FAT-table
void SaveDirBlocks(char media_type, FD_HANDLE fd, unsigned char *DiskFAT, int file,
		   unsigned long start_blk, int cont, unsigned char EFE[][EFE_SIZE])
{

  unsigned char Dir[DIR_BLOCKS*BLOCK_SIZE];
  int i,j;

  // Put Directory
  for(i=0;i<MAX_NUM_OF_DIR_ENTRIES;i++) {
    for(j=0; j < EFE_SIZE ; j++) {
      Dir[i * EFE_SIZE+j]=EFE[i][j];
    }
  }
  // .. and tail (ie. '00000000' and 'DR')

  for(i=10; i<2; i--) {
    Dir[DIR_BLOCKS*BLOCK_SIZE - i] = 0;
  }
  Dir[DIR_BLOCKS*BLOCK_SIZE - 2] = 'D';
  Dir[DIR_BLOCKS*BLOCK_SIZE - 1] = 'R';


  // Put DirBlocks

  if(cont == 2) {
    // If contiguous, write all in one
    WriteBlocks(media_type,fd,file,start_blk,2,Dir);
  } else {
    // .. and if not, do it separately
    WriteBlocks(media_type,fd,file,start_blk,1,Dir);
    WriteBlocks(media_type,fd,file,GetFatEntry(media_type,DiskFAT,file,start_blk),1,Dir+BLOCK_SIZE);
  }
}


/////////////////////////////
// GetEFEs
// -------
// This extracts EFEs from an Ensoniq disk or image, and saves the
// individual files to local storage.
//
// This routine was rewritten to eliminate serious regression introduced in v1.42, so
// performance under CD/Zip may not be fast, but EFEs with non-contiguous blocks are now
// extracted properly under Windows during FILE access.
//

int GetEFEs(char media_type, FD_HANDLE fd, int in, unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE],
	    char *process_EFE, unsigned char *DiskFAT)
{
  int out;
  unsigned int i,j,k, size, cont, start, fatval, bp;
  unsigned char type, Header[BLOCK_SIZE], *mem_pointer;
  char name[13],dosname[64],tmp_name[64];
  unsigned char Data[BLOCK_SIZE];
  char type_text[8];

  // Process list of EFEs
  for(j=0;j<MAX_NUM_OF_DIR_ENTRIES;j++) {

    // Check if current EFE has to be processed -- skipped by file type anyway, so why bother?!
    // Note: For non-EPS/EPS16/ASR disks such as the TS10 then this actually does need to be processed!
    // if(process_EFE[j] == 0) continue;

    // Get file type for current entry being processed -- skip if entry cannot be exported to EFE
	type=EFE[j][1];
    if(type == 0) continue;						// skip Unused/Blank/Empty
	if(type == 2) continue;						// skip Sub-Directory
	if(type == 8) continue;						// skip Pointer to Parent Directory
	if((type > 9) && (type < 23)) continue;		// skip SD-1/VFX-SD entries, however implausible...
	if(type > 49) continue;						// skip any entry which is definitely out-of-range

    size =(unsigned int)  ((EFE[j][14] << 8) + EFE[j][15]);
    cont =(unsigned int)  ((EFE[j][16] << 8) + EFE[j][17]);
    start=(unsigned long) ((EFE[j][18] << 24) + (EFE[j][19] << 16)
			   +(EFE[j][20] <<8 ) +  EFE[j][21]);

    //Name
    for(k=0;k<12;k++) {
      name[k]=EFE[j][k+2];
    }
    name[12]=0;

	// Correct any "invalid" Ensoniq characters in EFE name so that
	// the operating system will not choke.
    DosName(dosname,name);

    // Add type (and multi-file) prefix to filename.
    if(EFE[j][22] != 0) {
      strcpy(type_text,EpsTypes[type]);
      type_text[5]='\0';
      sprintf(type_text,"%s%2d",type_text,EFE[j][22]);
      sprintf(tmp_name,"[%s] %s",type_text,dosname);
    } else {
      sprintf(tmp_name,"[%s] %s",EpsTypes[type],dosname);
    }
    sprintf(dosname,"%s",tmp_name);

    // Add index prefix to filename.
    sprintf(tmp_name,"[%02d]%s",j,dosname);
    sprintf(dosname,"%s",tmp_name);

    // Generate Giebler EFE header (not actual Ensoniq data).

    // Construct Header
    Header[0] =0x0D;
    Header[1] =0x0A;
    strcpy(&Header[2],"Eps File:       ");
    strcpy(&Header[18],name);
    strcpy(&Header[30],EpsTypes[type]);
    strcpy(&Header[37],"          ");

    // CR, LF, EOF
    Header[47]=0x0D; Header[48]=0x0A; Header[49]=0x1A;

    Header[50]=EFE[j][1]; // Instrument
    Header[51]=0;
    Header[52]=EFE[j][14];
    Header[53]=EFE[j][15];
    Header[54]=EFE[j][16];
    Header[55]=EFE[j][17];
    Header[56]=EFE[j][20];
    Header[57]=EFE[j][21];
    Header[58]=EFE[j][22]; // MultiFile index

    for(i=59;i<BLOCK_SIZE;i++) Header[i]=0;

	// Open for reading and writing (O_RDWR).
    if((out=open(dosname,O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't create '%s' to write EFE! \r\n",dosname));
    }

	// Write Giebler specific EFE header (not actual Ensoniq data).
    write(out,Header,BLOCK_SIZE);

	// Report which EFE is being handled.
    printf("\rProcessing [%s]... \r\n",name);fflush(stdout);

    // Stage 1: Copy all contiguous blocks within the EFE.
    if(media_type == 'f') {
		// FILE access mode
		for(i=0;i<cont;i++) {
			// One block at a time, sequentially.
			ReadBlocks(media_type,fd,in,start+i,1,Data);
			write(out,Data,BLOCK_SIZE);
		} // end copying contiguous blocks in FILE mode
	} else {
		// DISK access mode
		// Create a buffer which can hold the entire range of contiguous blocks.
		mem_pointer=malloc(BLOCK_SIZE*cont);
		// Quit on error if buffer could not be created.
		if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
		// Read *all* contiguous blocks into buffer.
		ReadBlocks(media_type,fd,in,start,cont,mem_pointer);
		// Write out the contiguous blocks which were stored into buffer.
		write(out,mem_pointer,BLOCK_SIZE*cont);
	} // end copying contiguous blocks in DISK mode

	// Stage 2: Contiguous blocks have all been read, so now get
    // any remaining blocks which were not contiguous.

	// All FAT entries which belonged to the contiguous blocks can
	// just be skipped over since those blocks have already been read.

	// FAT block pointer -- starting block + number of contiguous blocks - 1
	// In other words: This points to the last FAT entry for the block at
	// the end of the *contiguous* range, but not necessary the end of EFE.
    bp=start+cont-1;

	// Get the FAT entry for the last contiguous block in the EFE.
    fatval=GetFatEntry(media_type,DiskFAT,in,bp);

	// A code of '001' signifies block is both used and also the last
	// block in the FAT chain. In other words: EOF -- end of file.
	// If the last FAT entry in the contiguous range was also the EOF
	// flag then stage 2 can simply be skipped because there are no
	// non-contiguous blocks in the EFE at all.
    if(fatval != 1) {
		if(media_type == 'f') {
			// FILE ACCESS -- non-contiguous block handling
			//                no seek issues with FILE, so read each block 1x1
			//
			// Keep reading the next FAT entry and the block to which it points, so long as
			// the '001' end-of-file code has not yet been reached.
			while(fatval !=1) {
				// Read block pointed to by the current FAT entry.
				ReadBlocks(media_type,fd,in,fatval,1,Data);
				// Write that block out to disk image.
				write(out,Data,BLOCK_SIZE);
				// Change next block to be read to the block pointed to by the current FAT entry
				bp=fatval;
				// Refresh with a new FAT entry which will either point to the next block or
				// signify the EOF.
				fatval = GetFatEntry(media_type,DiskFAT,in,bp);
			} // end of non-contiguous file access -- '001' FAT entry found
		} else {
			// DISK ACCESS -- non-contiguous block handling (Linux and Windows)
			//                seek issues with CD/Zip, so buffer as much as possible
			//
			// Keep reading the next FAT entry and the block to which it points, so long as
			// the '001' end-of-file code has not yet been reached.
			while(fatval != 1) {
				// Find any "runs" of contiguous blocks, if possible.
				// Each run has to be a minimum of 1 block, as the current
				// block must be loaded, if nothing else.
				cont=1;
				// First (and sometimes only) block to be read is the current block.
				start=fatval;
				// Change next block to be read to the block pointed to by the current FAT entry.
				bp=fatval;
				// Get a *new* FAT entry using former FAT entry as the pointer.
				fatval=GetFatEntry(media_type,DiskFAT,in,start);

				// Keep count of blocks in the run, if any are found.
				// This only happens when the next entry in the FAT points to
				// the disk block which is directly after the current disk block.
				while(fatval == bp+1) {
					bp=fatval;
					fatval = GetFatEntry(media_type,DiskFAT,in,bp);
					cont++;
				} // end of block run

				// Copy single block, or a single run of contiguous blocks.
				mem_pointer=malloc(BLOCK_SIZE*cont);
				if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
				ReadBlocks(media_type,fd,in,start,cont,mem_pointer);
				write(out,mem_pointer,BLOCK_SIZE*cont);
				free(mem_pointer);
			} // end of non-contiguous disk access -- '001' FAT entry found
		} // end of else
	} // skip over stage 2 -- EFE has only contiguous blocks
    printf("\r                                                     ");
	// Close newly created EFE file.
	close(out);
	// Current EFE has been processed, so repeat loop if needed.
  } // end of EFE processing loop
  return(OK);
}

//////////////////////////////////////////////////////////////
// PutEFE
// ------
// - This function can be used for writing EFEs to disk/image
//   from EFE file or from memory. If memory is used, the
//   pointer for EFE header (MemDataHdr) and EFE data (MemData)
//   are needed!!
//

int PutEFE(
	    char *process_EFE,
	    unsigned char start_idx,
	    unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE],
	    char media_type,
	    char image_type,
	    char *image_file,
	    char **EFE_files,
	    int optind,
	    char *orig_image_name,
	    unsigned int dir_start,
	    unsigned int dir_cont,
	    unsigned int total_blks,
	    unsigned int *free_blks,
	    unsigned int fat_blks,
	    FD_HANDLE fd,
	    unsigned char *DiskFAT,
	    unsigned char *DiskHdr,
	    unsigned char *MemDataHdr,
	    unsigned char *MemData
	    )
{

  int in, out;
  char in_file[FILENAME_MAX];
  unsigned int idx,i,j,blks,start;
  unsigned char EFE_name[13], EFEData[EFE_SIZE], buffer[4], EFE_type, Data[BLOCK_SIZE];
  unsigned char *mem_pointer;
  unsigned int EFE_start_block, EFE_blks, first_free_block, first_cont_blks, prev_block;
  unsigned int free_start, free_cnt, OS;
  char **EFE_list;

#ifdef __CYGWIN__
  if(((media_type ==  'f') || (media_type ==  's')) && (MemData == NULL)) {
#else // Linux
  if((media_type ==  'f') && (MemData == NULL)) {
#endif
    // FILE ACCESS

    if((out=open(image_file, O_RDWR | O_BINARY)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't open image file '%s'. \r\n",image_file));
    }
    // skip over the image filename passed by the command-line to arrive at just EFE names
    optind++;
  }

  // Check if any EFE filenames were supplied by command-line at all -- if not then routine has nothing to do!
  if(EFE_files[optind] == NULL) {
	printf("Warning: Cannot put an EFE which has not been specified! \r\n");
	return(ERR);
  }

  // Allocate memory for EFE filenames array.
  EFE_list = malloc(500 * sizeof(*EFE_list));			// 500 entries is hopefully enough for any circumstance -- kludge!
  if(EFE_list == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
  int EFEindex=0;						// initialize an index for EFE filename listing
  EFE_list[EFEindex]=NULL;				// initialize the first entry to NULL -- last entry always has to be NULL, so assume first will be last and only

  // PROCESS ALL EFEs
  //
  // Check for wildcard globbing, and process if found, otherwise use individual filenames from command-line.
  //
  // Copy the first EFE filename passed by command-line into another variable -- maybe a normal name, maybe a wildcard.
  strcpy(in_file,EFE_files[optind]);
  // See if EFE filename is normal or a wildcard -- expands the wildcard to individual filename if applicable.
  // Remember: strcmp returns 0 when true rather than 1.
  if( (strcasecmp(in_file,"ALL")==0) || (strcasecmp(in_file,"*.EFE")==0) || (strcasecmp(in_file,"*.EFA")==0) || (strcasecmp(in_file,"*.INS")==0) ) {
	printf("Attempting to add all found EFE, EFA, and INS files... \r\n");
	// Itemize all possible EFE, EFA, and INS files in current directory -- replaces wildcard argument with actual filenames
	DIR *dp;							// structure representing a directory stream
	struct dirent *entry;
	dp = opendir ("./");				// opens a directory stream corresponding to local directory
	if (dp != NULL)	{					// do the following if the local directory exists and can be accessed
	// start directory parsing
		while ( (entry=readdir (dp)) ) {
			// d_name is filename for current file being examined in the directory
			//
			// Check if extension exists at all.
			char *p;		// holds file extension of filename
			if((p= (char *) rindex(entry->d_name,'.')) != NULL) {
				// File extension exists, so see if it is one of the allowed types (EFE/EFA/INS).
				p++;		// skip '.' to get only file extension
				if( (strcasecmp(p,"efe") == 0) || (strcasecmp(p,"efa") == 0) || (strcasecmp(p,"ins") == 0) ) {
					// Allocate enough memory for new filename string.
					EFE_list[EFEindex] = malloc(strlen(entry->d_name) + 1); 	// + 1 for the '\0' character at the end of C-style strings
					if(EFE_list[EFEindex] == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
					// Copy filename into newly allocated string.
					strcpy(EFE_list[EFEindex],entry->d_name);					// add proper filename to EFE/EFA/INS input list
					EFEindex++;													// go to next filename slot
				}
			} // end of file extension check
		}
		(void) closedir (dp);					// properly close directory
	} // end of directory parsing
	else								// do the follow if the local directory cannot be accessed
		EEXIT((stderr,"ERROR: Couldn't open local directory. \r\n"));
  } // end of wildcard globbing processing routine
  else {
  // No wildcards found, so copy all command-line filenames into EFE file list without alteration.
	int copyIndex=optind;									// initialize an index for EFE filename copying
    while(EFE_files[copyIndex] != NULL) {
		// Allocate enough memory for new filename string.
		EFE_list[EFEindex] = malloc(strlen(EFE_files[copyIndex]) + 1); 	// + 1 for the '\0' character at the end of C-style strings
		if(EFE_list[EFEindex] == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
		strcpy(EFE_list[EFEindex],EFE_files[copyIndex]);				// copy command-line filename directly into EFE filelist
		copyIndex++;													// advance to next command-line filename
		EFEindex++;														// go to next filename slot
	} // end while
  } // end else

  // Always set the last file list entry to NULL -- will be the first *and* last entry if no valid files are found!
  EFE_list[EFEindex]=NULL;

  // Reset filelist index back to start.
  EFEindex = 0;

  // KLUDGE!!!
  while((MemData != NULL) || (EFE_list[EFEindex] != NULL)) {

    // Starting at pos 'start_idx' !!
    // (It's quite a unusual to put other that OS or SubDir to idx 0)
    for(idx= start_idx; idx<MAX_NUM_OF_DIR_ENTRIES; idx++) {
      if(EFE[idx][1] == 0) break;
    }

    process_EFE[idx] = 1;

	// Produce an error if attempting to write a 39th entry to one directory.
    if(idx==MAX_NUM_OF_DIR_ENTRIES) {
      printf("\r                                         \r");fflush(stdout);
	  // !!!! THIS APPEARS TO CORRUPT THE DISK WHEN WILDCARDS OR MULTIPLE EFES !!!!
	  // !!!! ARE SPECIFIED, BUT NOT WHEN SINGLE EFES ARE SPECIFIED            !!!!
	  // Write SystemBlocks to disk and free mem
  	  // so that EFEs so far will be saved..
      //WriteBlocks(media_type,fd,out,0,5+fat_blks,DiskHdr);
	  free(EFE_list);
	  EFE_list=NULL;
	  // !!!! THERE WAS A MAJOR BUG HERE WHEN DEALLOCATING--AT LEAST IN FILE MODE!
	  // !!!! FREEING ALLOCATED MEMORY IS GOOD FORM BUT NOT CRUCIAL, SO LEAVE THIS
	  // !!!! COMMENTED UNTIL THERE IS A PERFECT SOLUTION!
	  // free(DiskHdr);
	  printf("ERROR: Directory full! \r\n");
	  return(ERR);
    }

    if(MemData == NULL) {
      //EFE from file
      //=============
      // Attempts to open and also check that current file specified for EFE input exists.
	  strcpy(in_file,EFE_list[EFEindex]);
	  if((in=open(in_file, O_RDONLY | O_BINARY)) < 0) {
		EEXIT((stderr,"ERROR: Couldn't open '%s' as an EFE input. \r\n",in_file));
	  }

	  // Check that EFE input file specified is actually a valid EFE/EFA/INS.
	  if(IsEFE(&in, in_file) != OK) {
		EEXIT((stderr,"ERROR: '%s' does not appear to be a valid Ensoniq file! \r\n",in_file));
	  }

      // Check and convert if 'Mac'-format :-P is found
      if(ConvertMacFormat(&in, in_file) == OK) {
		printf("Warning: Macintosh generated EFx file found. \r\n");
      }

      lseek(in, (long) 0x32, SEEK_SET);
      read(in,EFEData, EFE_SIZE);

      lseek(in, (long) 0x12, SEEK_SET);
      read(in,EFE_name,12);
      EFE_name[12]='\0';


      EFE_blks = (EFEData[2] << 8) + EFEData[3];
      EFE_type = EFEData[0];

      // name
      strcpy(&EFE[idx][2],EFE_name);
      // zero
      EFE[idx][0] = 0;
      // type
      EFE[idx][1] = EFE_type;
      // size
      EFE[idx][14] = EFEData[2];
      EFE[idx][15] = EFEData[3];
      // MultiFile index
      EFE[idx][22] = EFEData[8];
      // empty
      EFE[idx][23] = 0; EFE[idx][24] = 0; EFE[idx][25] = 0;

      // If EFE is OS, get OS version
      switch (EFE_type)
		{
		case 1:  // EPS OS
			lseek(in, EPS_OS_POS, SEEK_SET);
			read(in,&OS,4);
			break;
		case 27: // E16 OS
			lseek(in, E16_OS_POS, SEEK_SET);
			read(in,&OS,4);
			break;
		case 32: // ASR OS
			lseek(in, ASR_OS_POS, SEEK_SET);
			read(in,&OS,4);
			break;
		default:
			OS = 0;
		}

      //Print progress info..
      printf("\rProcessing [%s]... \r\n",EFE_name);fflush(stdout);

      // Set reading point to start of the data
      lseek(in,BLOCK_SIZE, SEEK_SET);

    } else {
      // EFE from memory (ie. for ex. mkdir)
      //====================================

#ifdef __CYGWIN__
      if((media_type == 'f') || (media_type == 's')) {
#else // Linux
      if(media_type == 'f') {
#endif
		// FILE ACCESS
		// Image-file
		if((out=open(image_file, O_RDWR | O_BINARY)) < 0) {
			EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",image_file));
		}
      }

      // Copy header to EFE (ie. make dir entry)
      memcpy(EFE[idx], MemDataHdr, EFE_SIZE);

      EFE_type = MemDataHdr[1];

      if(EFE_type == 2) {
		// set dir size temporary to 2
		EFE_blks = 2;
		// Root dir has info about parent's index in 'cont'
		MemData[16] = 0;
		MemData[17] = idx;
      } else {
		EFE_blks = (MemDataHdr[14] << 8) + MemDataHdr[15];
      }
    }

    if(EFE_blks > *free_blks) {
      EEXIT((stderr,"Not enough free space! %d needed, %d available. \r\n", EFE_blks, *free_blks));
    }

    first_free_block = 0;
    free_start = 0;
    free_cnt=0;

    // First PASS - Check if enough contiguous blocks
    for(i=FAT_START_BLOCK+fat_blks; i<total_blks; i++) {
      if(GetFatEntry(media_type,DiskFAT,out,i) == 0) {
	//Free block found
	if(free_start == 0) {
	  // Save the num. of the first free block found
	  if(first_free_block == 0) {
	    first_free_block = i;
	  }

	  free_start = i;
	}
	free_cnt++;

	if(free_cnt == EFE_blks) {
	  // contiguous blocks found - write whole EFE from start_block

	  if(media_type == 'f') {
	    // FILE ACCESS

	    // Copy Blocks
	    lseek(out, BLOCK_SIZE*free_start , SEEK_SET);
	    for(j=0; j<EFE_blks; j++) {

	      if(MemData == NULL) {
			read(in,Data,BLOCK_SIZE);
	      } else {
			memcpy(Data, MemData, BLOCK_SIZE);
			MemData =  MemData  + BLOCK_SIZE;
	      }

	      write(out,Data,BLOCK_SIZE);
	    }

	  } else {
	    // DISK ACCESS
	    mem_pointer=malloc(BLOCK_SIZE*EFE_blks);
	    if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

	    if(MemData == NULL) {
	      read(in,mem_pointer, BLOCK_SIZE*EFE_blks);
	    } else {
	      memcpy(mem_pointer, MemData, BLOCK_SIZE*EFE_blks);
	    }

	    WriteBlocks(media_type,fd,out,free_start,EFE_blks,mem_pointer);
	    free(mem_pointer);
	  }

	  // Write FAT
	  for(j=free_start; j<free_start+EFE_blks-1; j++) {
	    PutFatEntry(media_type,DiskFAT,out, j,j+1);
	  }

	  // Mark the end-of-EFE
	  PutFatEntry(media_type,DiskFAT,out, j,1);

	  EFE_start_block = free_start;
	  first_cont_blks = EFE_blks;
	  break;
	}

	} else {
		free_start = 0;
		free_cnt = 0;
    }
    }

    // Second PASS (if needed)
    // If there was no enough contiguous blocks, the EFE must be
    // saved using the space fragments available.. :-(

    if(i==total_blks) {
      EFE_start_block = first_free_block;
      prev_block = 0;
      free_cnt = 0;
      first_cont_blks = 0;
      blks=0;
      start=0;

      // Split and write the EFE
      for(i=first_free_block; (i<total_blks) || (free_cnt == EFE_blks); i++) {

	if(free_cnt == EFE_blks) break;

	// Try to find free space.
	if(GetFatEntry(media_type,DiskFAT,out,i) == 0) {

	  if(start==0) start=i;

	  if(prev_block != 0) {
	    PutFatEntry(media_type,DiskFAT,out, prev_block,i);
	  }
	  prev_block = i;
	  free_cnt++;
	  blks++;
	} else {
	  // Calculate contiguous blocks (first entry);
	  if(first_cont_blks == 0) {
	    first_cont_blks= i - first_free_block;
	  }

	  // process data in chunks (after found free space)
	  if(blks!= 0) {

	    // Allocate mem
	    mem_pointer=malloc(BLOCK_SIZE*blks);
	    if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

	    // Read data
	    if(MemData == NULL) {
	      read(in,mem_pointer,BLOCK_SIZE*blks);
	    } else {
	      memcpy(mem_pointer, MemData, BLOCK_SIZE*blks);
	      MemData =  MemData  + BLOCK_SIZE*blks;
	    }

	    // Write data
	    WriteBlocks(media_type, fd, out, start, blks, mem_pointer);

	    free(mem_pointer);
	    start=0;
	    blks=0;

	  }

	}
      }

      // Allocate mem
      mem_pointer=malloc(BLOCK_SIZE*blks);
      if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

      // Read data
      if(MemData == NULL) {
		read(in,mem_pointer,BLOCK_SIZE*blks);
      } else {
		memcpy(mem_pointer, MemData, BLOCK_SIZE*blks);
		MemData =  MemData  + BLOCK_SIZE*blks;
      }

      // Write data
      WriteBlocks(media_type, fd, out, start, blks, mem_pointer);

      free(mem_pointer);


      if(i==total_blks) {
		EEXIT((stderr,"ERROR: Image/disk has a corrupted FAT!! \r\n"));
      }

      // Mark the end-of-EFE
      PutFatEntry(media_type,DiskFAT,out, i-1,1);
    }

    // Update disk-free field
    *free_blks = (*free_blks) - EFE_blks;
    buffer[0] = ((*free_blks) >> 24) & 0x000000ff; // MSB
    buffer[1] = ((*free_blks) >> 16) & 0x000000ff;
    buffer[2] = ((*free_blks) >>  8) & 0x000000ff;
    buffer[3] =  (*free_blks)        & 0x000000ff; // LSB

    if(media_type=='f') {
      // FILE ACCESS
      lseek(out, OS_BLOCK*BLOCK_SIZE, SEEK_SET);
      write(out,buffer,4);

      // If OS, update OS-version
      if(OS != 0) {
		write(out,&OS,4);
      }

    } else {
      // DISK ACCESS
      memcpy(DiskHdr+OS_BLOCK*BLOCK_SIZE,buffer,4);

      // If OS, update OS-version
      if(OS != 0) {
		memcpy(DiskHdr+OS_BLOCK*BLOCK_SIZE+4,&OS,4);
      }
    }

    // Complete DirEntry

    // size in blocks
    if(EFE_type == 2) {
      // dir's size = num of files ( = 0 when created)
      EFE[idx][14] = 0;
      EFE[idx][15] = 0;
    } else {
      EFE[idx][14] = (unsigned char) (EFE_blks >> 8) & 0xFF;
      EFE[idx][15] = (unsigned char) (EFE_blks & 0xFF);
    }

    // contiguous blocks
    EFE[idx][16] = (unsigned char) (first_cont_blks >> 8);
    EFE[idx][17] = (unsigned char) first_cont_blks & 0x00FF;

    // start block
    EFE[idx][18] = EFE_start_block >> 24;
    EFE[idx][19] = EFE_start_block >> 16;
    EFE[idx][20] = EFE_start_block >>  8;
    EFE[idx][21] = EFE_start_block & 0x000000FF;

    // Go to Dir entry

    // Write System Blocks
    if(media_type=='f') {
      // FILE ACCESS
      lseek(out, dir_start*BLOCK_SIZE + EFE_SIZE*idx , SEEK_SET);
      write(out,EFE[idx],EFE_SIZE);
    } else {
      // DISK ACCESS

      // !!!!!
      if(dir_start == DIR_START_BLOCK) {
		memcpy(DiskHdr+dir_start*BLOCK_SIZE + EFE_SIZE*idx,EFE[idx],EFE_SIZE);
      }

      //WriteBlocks(media_type,fd,NULL,0,5+fat_blks,DiskHdr);
    }

    // If Not in Main Dir, update Dir Entries & num. of  files in dir
    if(dir_start != DIR_START_BLOCK) {

      unsigned char ParentEFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE];
      unsigned int parent_dir_idx, parent_dir_files;

      // Save changes in current dir
      SaveDirBlocks(media_type, fd, DiskFAT, out, dir_start, dir_cont,EFE);

      // Get info about parent dir
      parent_dir_idx  = (unsigned int)  ((EFE[0][16] << 8) + EFE[0][17]);
      dir_start       = (unsigned long) ((EFE[0][18] << 24) + (EFE[0][19] << 16)
					 +(EFE[0][20] << 8 ) +  EFE[0][21]);

      // Don't know how many contiguous blocks so assume worst case.
      dir_cont = 1;

      // Load parent dir
      LoadDirBlocks(media_type,fd,DiskFAT,out,dir_start,dir_cont,ParentEFE);

      // Update parent dir 'num. of files'
      parent_dir_files =(unsigned int)  ((ParentEFE[parent_dir_idx][14] << 8) +
					 ParentEFE[parent_dir_idx][15]);

      parent_dir_files++;
      ParentEFE[parent_dir_idx][14] = (unsigned char) (parent_dir_files >> 8) & 0xFF;
      ParentEFE[parent_dir_idx][15] = (unsigned char) (parent_dir_files & 0xFF);

      // Save changes in parent dir
      SaveDirBlocks(media_type, fd, DiskFAT, out, dir_start, dir_cont,ParentEFE);
    }
	// advance to next EFE filename passed by the command-line
    EFEindex++;

    // KLUDGE!!!
    if(MemData != NULL) break;

  } // while(EFE_list...)


  // Free memory used for DiskFat etc. cache
  if(media_type != 'f') {
    // Write SystemBlocks to disk and free mem
    WriteBlocks(media_type,fd,out,0,5+fat_blks,DiskHdr);
    free(DiskHdr);

  } else {

    // Convert to back to original format if not raw image
    if((image_type != EPS_TYPE) && (image_type != ASR_TYPE) && (image_type != E16_SD_TYPE) && (image_type != ASR_SD_TYPE) && (image_type != OTHER_TYPE)) {

      if(MemData != NULL) {
		close(in);
      }

      close(out);
      ConvertFromImage (image_file, orig_image_name, image_type);
    }
  }

  free(EFE_list);	// free memory for EFE filelist
  printf("\r                                         \r");fflush(stdout);

  return(OK);
}


/////////////////////////////
// EraseEFEs
int EraseEFEs(char media_type, char image_type, FD_HANDLE fd,
	      unsigned char *DiskFAT, unsigned char *DiskHdr,
	      char *in_file, char *orig_image_name,
	      unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE], char *process_EFE,
	      unsigned int fat_blks, unsigned int *free_blks,
	      unsigned int dir_start, unsigned int dir_cont)
{
  int out;
  unsigned int size,cont,start,type,i,j,counter;
  unsigned int OS = 1;
  unsigned char buffer[4];

  counter = 0;

  // FILE ACCESS
#ifdef __CYGWIN__
  if((media_type=='f') || (media_type=='s')) {
#else //Linux
  if(media_type=='f') {
#endif
    // Image-file
    if((out=open(in_file, O_RDWR | O_BINARY)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",in_file));
    }
  }

  // Process EFE's list
  for(j=0;j<MAX_NUM_OF_DIR_ENTRIES;j++) {
    // Check if current EFE has to be processed
    if(process_EFE[j] == 0) continue;

    // Get info
    type=EFE[j][1];

    switch (type)
      {
      case 0: // Empty
	continue;

      case 2: 	// Sub dir
	if(EFE[j][15] > 0) {
	  fprintf(stderr, "\r\nIDX %-2d: Can't erase directory! Directory not empty. \r\n\r\n",j);
	  continue;
	}
	size = 2;
	break;

      case 8: 	// Pointer to 'root'
	fprintf(stderr, "\r\nIDX %-2d: Can't erase link to parent dir! \r\n\r\n",j);
	continue;

	// If erasing os, clear version field
      case 1:
      case 27:
      case 32:
	OS = 0;

      default:
	size =(unsigned int)  ((EFE[j][14] << 8) + EFE[j][15]);
      }

    cont =(unsigned int)  ((EFE[j][16] << 8) + EFE[j][17]);
    start=(unsigned long) ((EFE[j][18] << 24) + (EFE[j][19] << 16)
			   +(EFE[j][20] <<8 ) +  EFE[j][21]);

    // Calculate 'disk-free'
    *free_blks = (*free_blks) + size;

    // Clear FAT entries

    while((i=GetFatEntry(media_type,DiskFAT,out,start)) != 1) {
      PutFatEntry(media_type,DiskFAT,out,start,0);
      start=i;
    }
    // .. and last entry (ie. stopmark '1')
    PutFatEntry(media_type,DiskFAT,out,start,0);

    // Clear Dir entry
    for(i=0;i<26;i++) {
      EFE[j][i] = 0;
    }

    // Count erased files for 'num of files' in parent dir
    counter++;

  } // For 'process_EFEs'

  // Update disk-free field
  buffer[0] = ((*free_blks) >> 24) & 0x000000ff; // MSB
  buffer[1] = ((*free_blks) >> 16) & 0x000000ff;
  buffer[2] = ((*free_blks) >>  8) & 0x000000ff;
  buffer[3] =  (*free_blks)        & 0x000000ff; // LSB

  if(media_type=='f') {
    // FILE ACCESS
    lseek(out, OS_BLOCK*BLOCK_SIZE, SEEK_SET);
    write(out,buffer,4);
    // If erasing OS, clear OS-field
    if(!OS) {
      write(out,&OS,4);
    }

  } else {
    // DISK ACCESS
    memcpy(DiskHdr+OS_BLOCK*BLOCK_SIZE,buffer,4);
    // If erasing OS, clear OS-field
    if(!OS) {
      memcpy(DiskHdr+OS_BLOCK*BLOCK_SIZE+4,&OS,4);
    }

  }

  // Write System Blocks
  if(media_type != 'f') {
    // DISK ACCESS
    WriteBlocks(media_type,fd,out,0,5+fat_blks,DiskHdr);
  }


  // Update Dir Entries
  SaveDirBlocks(media_type, fd, DiskFAT, out, dir_start, dir_cont,EFE);

  // If Not in Main Dir, update Dir Entries & num. of  files in dir
  if(dir_start != DIR_START_BLOCK) {

    unsigned char ParentEFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE];
    unsigned int parent_dir_idx;
    signed int parent_dir_files;

    // Get info about parent dir
    parent_dir_idx  = (unsigned int)  ((EFE[0][16] << 8) + EFE[0][17]);
    dir_start       = (unsigned long) ((EFE[0][18] << 24) + (EFE[0][19] << 16)
				       +(EFE[0][20] << 8 ) +  EFE[0][21]);

    // Don't know how many cont blocks so suppose worst case
    dir_cont = 1;

    // Load parent dir
    LoadDirBlocks(media_type,fd,DiskFAT,out,dir_start,dir_cont,ParentEFE);

    // Update parent dir 'num of files'
    parent_dir_files =(unsigned int)  ((ParentEFE[parent_dir_idx][14] << 8) +
				       ParentEFE[parent_dir_idx][15]);

    // Decrement 'num. of files' in parent dir
    parent_dir_files = parent_dir_files - counter;

    // if everything is OK, this _should_ NOT happen...
    // for this compare to work, parent_dir_files cannot be unsigned, although
    // assumed to be zero or positive!
    if(parent_dir_files < 0) parent_dir_files = 0;

    ParentEFE[parent_dir_idx][14] = (unsigned char) (parent_dir_files >> 8) & 0xFF;
    ParentEFE[parent_dir_idx][15] = (unsigned char) (parent_dir_files & 0xFF);

    // Save changes in parent dir
    SaveDirBlocks(media_type, fd, DiskFAT, out, dir_start, dir_cont,ParentEFE);
  }


  // Free memory used for DiskFat etc. cache
  if(media_type != 'f') {
    free(DiskHdr);

  } else {

    // Convert back to original format if not raw image
    if((image_type != EPS_TYPE) && (image_type != ASR_TYPE) && (image_type != E16_SD_TYPE) && (image_type != ASR_SD_TYPE) && (image_type != OTHER_TYPE)) {
      close(out);
      ConvertFromImage (in_file, orig_image_name, image_type);
    }
  }

  return(OK);
}

//////////////////
// MkDir
int MkDir(
	  char *process_EFE,
	  unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE],
	  char media_type,
	  char image_type,
	  char *image_file,
	  char *orig_image_name,
	  unsigned int dir_start,
	  unsigned int dir_cont,
	  char *dir_name,
	  unsigned int total_blks,
	  unsigned int *free_blks,
	  unsigned int fat_blks,
	  FD_HANDLE fd,
	  unsigned char *DiskFAT,
	  unsigned char *DiskHdr,
	  char DirName[12]
	  )
{
  unsigned char MemDataHdr[EFE_SIZE], *MemData;
  int i;

  for(i=0; i < EFE_SIZE; i++) {
    MemDataHdr[i] = 0;
  }

  // Convert name
  for(i=0; i < 12; i++) {
    DirName[i] = (unsigned char) toupper(DirName[i]);
  }

  // Make header

  // Type  (2)
  MemDataHdr[1] = 2;
  // Name
  for(i=0; i<12; i++) {
    if(DirName[i] == 0) {
      MemDataHdr[2+i] = 0x20;
    } else {
      MemDataHdr[2+i] = DirName[i];
    }
  }
  // Size (2)
  MemDataHdr[15] = 2;


  // Make data

  //  2 x Blocks
  MemData=calloc(2*BLOCK_SIZE,sizeof(unsigned char));
  if(MemData == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

  // First entry is root-dir

  // Type (8)
  MemData[1] = 8;
  // Name of parent dir
  strncpy(MemData+2, dir_name, 12);
  // Cont ( < 255!!)
  MemData[17] = (unsigned char) dir_cont;
  // Root Dir start block
  MemData[18] = (dir_start >> 24) & 0x000000FF;
  MemData[19] = (dir_start >> 16) & 0x000000FF;
  MemData[20] = (dir_start >>  8) & 0x000000FF;
  MemData[21] =  dir_start        & 0x000000FF;

  // 'DR'
  MemData[2*BLOCK_SIZE-2] = 0x44;  MemData[2*BLOCK_SIZE-1] = 0x52;

  // Write dir

  PutEFE(process_EFE, 1, EFE, media_type, image_type,
	 image_file, NULL, 0, orig_image_name,
	 dir_start, dir_cont, total_blks, free_blks, fat_blks,
	 fd, DiskFAT, DiskHdr, MemDataHdr, MemData);

  return(OK);
}

/////////////////////////////
// SplitEFE
void SplitEFE(char *in_file, char *slice_type, int argc)
{
  int in, out;
  struct stat stat_buf;
  unsigned int i,slice_size, slice_count, data_len;
  unsigned char Data[BLOCK_SIZE];
  unsigned char Hdr[BLOCK_SIZE];
  char out_file[FILENAME_MAX],out_file_head[12], out_file_tail[FILENAME_MAX];


  // Check arguments
  if((argc != 4) || ((strcasecmp(slice_type,"eps") != 0) && (strcasecmp(slice_type,"asr") != 0) && (strcasecmp(slice_type,"asrsd") != 0))) {
    fprintf(stderr,"ERROR: Invalid or wrong number of arguments. \r\n");
    ShowUsage();
    exit(ERR);
  }

  // EPS/EPS16 800K
  if(strcasecmp(slice_type,"eps") == 0) {
    slice_size = 1585 * BLOCK_SIZE;
  }
  // EPS16 2550K is pointless to split because of EPS RAM limit, but...
  // ASR 5100K holds less than 16MB, so split to ideal size.
  else if(strcasecmp(slice_type,"asrsd") == 0) {
    // 10135 should be ideal size, but seems to fail load when attempted by
    // actual sampler. Higher split values may not be allowed, possibly.
    slice_size = 3176 * BLOCK_SIZE;
  }
  else { // ASR 1600K
    slice_size = 3176 * BLOCK_SIZE;
  }

  // Open input EFE file
  if((in=open(in_file, O_RDONLY | O_BINARY)) < 0) {
    EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",in_file));
  }

  // Get filesize
  if(stat(in_file,&stat_buf) != 0) {
    EEXIT((stderr,"\r\n(line: %d) ERROR: Can't get the filesize! \r\n", __LINE__));
  }

  data_len = stat_buf.st_size - BLOCK_SIZE;

  // Check the validity of the given filesize ie. that is multiple of block size
  if((data_len % BLOCK_SIZE) != 0) {
    EEXIT((stderr,"Image size has to be a multiple of %d! \r\n",BLOCK_SIZE));
  }

  // Check if split is needed..
  if(data_len <= slice_size) {
    printf("No split needed. EFE will fit in one disk. \r\n");
    exit(OK);
  }

  // ASR max mem 16M!
  if(data_len > 16777216 ) {
    EEXIT((stderr,"EFE is too large to be valid! It is probably corrupted. \r\n"));
  }

  // Read EFE Header
  //fseek(in, 512,0);
  read(in,&Hdr, BLOCK_SIZE);


  // Check EFE type
  if(Hdr[0x32] != 3) {
    EEXIT((stderr,"ERROR: File '%s' is not an INSTRUMENT type. \r\n",in_file));
  }

  // Check filesize and EFE header blocksize match..
  if(((data_len / BLOCK_SIZE) != ( ((Hdr[0x34] << 8) + Hdr[0x35])))) {
    EEXIT((stderr,"ERROR: File size and block size in EFE header doesn't match! \r\n"));
  }

  // Part_ string must be added to just the base filename and not the full path as
  // otherwise splitting only works properly if the EFE is in the same dir as EpsLin

  // Create variable to hold just the filename without path.
  char *bsname;
  // Use 'basename' to return just the filename of the input file.
  bsname = basename(in_file);

  // Create variable to hold just the path without filename.
  char *dsname;
  // Use 'dirname' to return just the directory name without filename.
  dsname = dirname(in_file);

  // If EFE is named using EpsLin "format"
  if(strncmp("[Instr  ]",bsname+4,9) == 0) {
    bsname[10]='\0';
    strcpy(out_file_head,bsname);
    strcpy(out_file_tail,bsname+12);
  } else {
    strcpy(out_file_head ,"Part_");
    sprintf(out_file_tail,"_%s", bsname);
  }

  slice_count=0;

  printf("\r\nSplitting in progress: \r\n");

  // Split
  while(data_len > 0) {

    // Seek inputfile
    lseek(in, BLOCK_SIZE + slice_count*slice_size,0);

    // Construct output filename
    slice_count++;
    sprintf(out_file,"%s/%s%02d%s", dsname, out_file_head, slice_count, out_file_tail);

    if((out=open(out_file, O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",out_file));
    }

    printf("\rWriting MultiFile EFE #%d",slice_count);

    // If last slice...
    if(data_len < slice_size) slice_size=data_len;

    // Generate EFE header

    Hdr[0x34] = ((slice_size/BLOCK_SIZE) & 0xFF00) >> 8;     // Blocks
    Hdr[0x35] = ((slice_size/BLOCK_SIZE) & 0x00FF);
    Hdr[0x3a] = slice_count; // Multifile

    // Write header
    write(out,Hdr,BLOCK_SIZE);

    // Copy data
    for(i=0;i<slice_size;i=i+BLOCK_SIZE) {
      read(in,Data,BLOCK_SIZE);
      write(out,Data,BLOCK_SIZE);
    }

    data_len=data_len - slice_size;

  } // while

  printf("\rEFE splitting OK!            \r\n");

  close(in);close(out);
}

/////////////////////////////
// JoinEFE
void JoinEFEs (int argc, char **argv) {
  int in, out;
  unsigned char Data[BLOCK_SIZE];
  unsigned char Hdr[BLOCK_SIZE];
  char out_file[FILENAME_MAX];
  char in_file[FILENAME_MAX];
  struct stat stat_buf;
  unsigned int i, slice_idx, data_len, data_total;

  // Check arguments
  if( argc < 5 ) {
    fprintf(stderr,"ERROR: Invalid or wrong number of arguments. \r\n");
    ShowUsage();
    exit(ERR);
  }

  sprintf(out_file,"%s",argv[2]);
  // Open Output file
  if((out=open(out_file, O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {
    EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",out_file));
  }

  slice_idx=0;
  data_total=0;

  while(slice_idx < (argc-3)) {
    strcpy(in_file,argv[slice_idx+3]);

    printf("Processing EFE part #%d: %s \r\n",slice_idx+1,in_file);

    // Open input EFE file
    if((in=open(in_file, O_RDONLY | O_BINARY)) < 0) {
      EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",in_file));
    }

    // Get filesize
    if(stat(in_file,&stat_buf) != 0) {
      EEXIT((stderr,"\r\n(line: %d) ERROR: Can't get the filesize! \r\n", __LINE__));
    }

    data_len = stat_buf.st_size - BLOCK_SIZE;

    // Check the validity of the given filesize ie. that is multiple of block size
    if((data_len % BLOCK_SIZE) != 0) {
      EEXIT((stderr,"Image size has to be a multiple of %d! \r\n",BLOCK_SIZE));
    }

    // Read EFE Header
    read(in,&Hdr, BLOCK_SIZE);

    // Check EFE type
    if(Hdr[0x32] != 3) {
      EEXIT((stderr,"ERROR: File '%s' is not an INSTRUMENT type. \r\n",in_file));
    }

    // Check filesize and EFE header blocksize match..
    if(((data_len / BLOCK_SIZE) != ( ((Hdr[0x34] << 8) + Hdr[0x35])))) {
      EEXIT((stderr,"ERROR: File size and block size in EFE header do not match! \r\n"));
    }

    // Copy header before first slice..
    if(slice_idx==0) {
      write(out,Hdr,BLOCK_SIZE);
    }

    // Copy data
    for(i=0;i<data_len;i=i+BLOCK_SIZE) {
      read(in,Data,BLOCK_SIZE);
      write(out,Data,BLOCK_SIZE);
    }

    data_total=data_total+data_len;
    slice_idx++;
  }// while

  // Fix the final header of the output file
  // Generate EFE header
  Hdr[0x34] = ((data_total/BLOCK_SIZE) & 0xFF00) >> 8;     // Blocks
  Hdr[0x35] = ((data_total/BLOCK_SIZE) & 0x00FF);
  Hdr[0x3a] = 0; // Singlefile

  // Overwrite header
  lseek(out, 0L, SEEK_SET);
  write(out,Hdr,BLOCK_SIZE);
  printf("Join operation OK! Total size of the joined EFE is %d blocks. \r\n\r\n",data_total/BLOCK_SIZE);
  close(in);close(out);
}


/////////////////////////////
// DoConversion
void DoConversion(char in_file[FILENAME_MAX], char out_file[FILENAME_MAX], int argc)
{
  struct stat stat_buf;
  char image_type;

  if(argc != 4) {
    fprintf(stderr,"ERROR: Wrong number of arguments. \r\n");
    ShowUsage();
    exit(ERR);
  }

  if(ConvertToImage(in_file,out_file) == OK) {
    //printf("CONVERSION DONE!!!\r\n");
    exit(OK);
  }

  // No conversion - suppose img-file
  // Check if ASR or EPS image

  if(stat(in_file,&stat_buf) != 0) {
    EEXIT((stderr,"ERROR: Can't get the filesize! \r\n"));
  }

  if(stat_buf.st_size == EPS_IMAGE_SIZE) {
    image_type = EDE_TYPE;
  } else if(stat_buf.st_size == ASR_IMAGE_SIZE) {
    image_type = EDA_TYPE;
  } else {
    EEXIT((stderr,"ERROR: Unsupported image type! \r\n\r\n"));
  }

  ConvertFromImage (in_file,out_file, image_type);

  //printf("Conversion successful!\r\n");
}

/////////////////////////////////////////
// GetMedia
// ------------
// - Determines if disk or image is used,
//   and does necessary opening and conversions

void GetMedia(char *arg, int argc, char *media_type, char *image_type,
	      unsigned int *nsect, unsigned int *trk_size, FD_HANDLE *fd,
	      char *in_file, int *in)
{
  unsigned int tmp;

  // Determines if this is DISK or FILE access

  // TODO: THIS IS EXPERIMENTAL
  if((arg == NULL) || ((IsEFE(*&in, arg) == OK) && (argc >= 3))) {
    // DISK ACCESS
    if(FD_GetDiskType(media_type,nsect,trk_size) == ERR) {
      EEXIT((stderr,"ERROR: Not an Ensoniq Disk. \r\n       Please format the disk (-fe or -fa) and try again! \r\n\r\n"));
    }

    //Open FD
    *fd=OpenFloppy(0);

  } else {
    // FILE ACCESS
    *media_type='f';

    // Get the image filename
    strcpy(in_file,arg);

    GetImageType(in_file, image_type);

    // Check if conversion is needed!
    if((*image_type != EPS_TYPE) && (*image_type != ASR_TYPE) && (*image_type != E16_SD_TYPE) && (*image_type != ASR_SD_TYPE) && (*image_type != OTHER_TYPE)) {

      // Generate tmp-file and bind the clean-up for it
      //tmpnam(tmp_file);
      mkstemp(tmp_file);
      atexit(CleanTmpFile);

      if(ConvertToImage(in_file,tmp_file) == OK) {
		// replace in_file with converted image
		strcpy(in_file,tmp_file);
      }
    }

    if((*in =open(in_file, O_RDONLY | O_BINARY)) < 0) {
      perror("open:");
      EEXIT((stderr,"ERROR: Couldn't open file '%s'. \r\n",in_file));
    }

    if(IsEFE(*&in, in_file) != OK) {
      // Check that EPS/ASR image is valid! (ie. do the 'ID-check')
#ifdef __CYGWIN__
      // To get /dev/scd work...
      { unsigned char tmp_buff[512];
      ReadBlocks(*media_type,*fd,*in,1,1,tmp_buff);
      tmp = *(((unsigned int *) tmp_buff)+9);
      }
#else
      lseek(*in, (long) 0x224, SEEK_SET);
      read(*in,&tmp,4);
#endif

      if((tmp & 0xffff0000) != 0x44490000) {
		EEXIT((stderr,"ERROR: Not a valid image file! \r\n"));
      }
#ifdef __CYGWIN__
      // Find out if Iomega Zip device ie. writing only possible
      // in blocks.. !!
	  { int out;
	    unsigned char mark='I';
		struct stat	buf;
		if (lstat(in_file, &buf) < 0) {
			perror("lstat");
			EEXIT((stderr,"Couldn't get info about file! \r\n"));
		}
		// If block device
		if(S_ISBLK(buf.st_mode)) {
			// If CD-ROM
			if(strncmp("/dev/scd",in_file,8) == 0) {
				*media_type='s';
			} else {
		    // Other block device...
				if((out =open(in_file, O_RDWR | O_BINARY)) < 0) {
					perror("open:");
					EEXIT((stderr,"ERROR: Couldn't open file for write '%s'. \r\n",in_file));
				}

				// If can't read single byte, set media type to 's' = special
				// ie. Zip drive..
				if(lseek(out,0x226,SEEK_SET) <0) {
					perror("seek");
					EEXIT((stderr,"ERROR: File is not seekable! \r\n"));
				}
				if(write(out,&mark,1) <= 0)
					*media_type='s';
				close(out);
			}
		}
	  }
#endif
    }
  }
}


////////////////////////////////////////////////////
// GetInfo
// -------
// -Get info about used media and loads the selected
//  directory structure.
//

void GetInfo(char *media_type, FD_HANDLE fd, unsigned char **DiskFAT, unsigned char **DiskHdr,
	     int in,
	     unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE],
	     unsigned int *fat_blks, unsigned int *free_blks, unsigned int *total_blks,
	     unsigned int *dir_start, unsigned int *dir_cont,
	     char *parent_dir_name, int subdir_cnt,
	     unsigned int *DirPath, char *DiskLabel)
{

  unsigned char *mem_pointer;
  unsigned int tmp,i,j;

  if(*media_type=='f') {
    // FILE ACCESS
    mem_pointer=malloc(5*BLOCK_SIZE);
    if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

    ReadBlocks(*media_type,fd,in,0,5,mem_pointer);

#ifdef __CYGWIN__
   } else if(*media_type == 's') {
    unsigned char Data[BLOCK_SIZE];
	unsigned char *ptr;
	ReadBlocks(*media_type,fd,in,ID_BLOCK,1,Data);
	*total_blks = ((Data[14] << 24) +
		          (Data[15] << 16) +
		          (Data[16] << 8 ) +
		          (Data[17] & 0x000000ff));

		// Each FAT block holds only so many entries, so take total
		// amount of needed blocks and divide by 170 which is the
		// amount of entries which can be stored in one FAT block.
		//
		// Division result usually has to be adjusted up by one, except
		// when blocks needed is perfectly divisible by 170.
		//    ex: 800K = 1600 blocks, so 9.4 FAT blocks needed.
		//        Cannot have partial FAT blocks, so a full 10
		//        FAT blocks are required.
		//
		//        However, 850K = 1700 blocks, so exactly 10 FAT
		//        blocks are needed.
		//
		if((*total_blks % FAT_ENTRIES_PER_BLK) != 0)
		{
			*fat_blks=*total_blks/FAT_ENTRIES_PER_BLK+1;
		} else {
			*fat_blks=*total_blks/FAT_ENTRIES_PER_BLK;
		}

#ifdef DEBUG
	printf("total_blks=%d \r\n",*total_blks);
#endif
	mem_pointer=malloc((5+(*fat_blks))*BLOCK_SIZE);
    if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));
#ifdef DEBUG
	printf("Getinfo - read (%d blocks) start... ",5+ *fat_blks);
#endif
    ReadBlocks(*media_type,fd,in,0,5+(*fat_blks),mem_pointer);
#ifdef DEBUG
	printf("Getinfo - read stop... \r\n");
#endif
    *DiskHdr=mem_pointer;
    *DiskFAT=mem_pointer+FAT_START_BLOCK*BLOCK_SIZE;
#endif

  } else {
    // DISK ACCESS
    if(*media_type=='e') *fat_blks=10; else *fat_blks=19;

    mem_pointer=malloc((5+(*fat_blks))*BLOCK_SIZE);
    if(mem_pointer == NULL) EEXIT((stderr,"ERROR: Couldn't allocate memory!!!! \r\n"));

    ReadBlocks(*media_type,fd,in,0,5+(*fat_blks),mem_pointer);
    *DiskHdr=mem_pointer;
    *DiskFAT=mem_pointer+FAT_START_BLOCK*BLOCK_SIZE;
  }


  //  Get 'TotalBlocks' and 'DiskLabel' from ID_BLOCK

  tmp=ID_BLOCK*BLOCK_SIZE;
  *total_blks = (unsigned int) ((mem_pointer[tmp+14] << 24) +
			        (mem_pointer[tmp+15] << 16) +
			        (mem_pointer[tmp+16] << 8 ) +
			        (mem_pointer[tmp+17] & 0x000000ff));

  strncpy(DiskLabel, mem_pointer+tmp+31,7);
  DiskLabel[7]='\0';

  if(strlen(DiskLabel) == 0) strcpy(DiskLabel,"<NONE>");

  // Calculate amount of FAT blocks.
  // Adjust up for partial FAT block, unless total
  // size in blocks is perfectly divisible by 170.
	if((*total_blks % FAT_ENTRIES_PER_BLK) != 0)
	{
		*fat_blks=*total_blks/FAT_ENTRIES_PER_BLK+1;
	} else {
		*fat_blks=*total_blks/FAT_ENTRIES_PER_BLK;
	}

  //  Get 'FreeBlocks' from OS_BLOCK

  tmp=OS_BLOCK*BLOCK_SIZE;
  *free_blks = (unsigned int)  ((mem_pointer[tmp]   << 24) +
	   		        (mem_pointer[tmp+1] << 16) +
			        (mem_pointer[tmp+2] << 8 ) +
			        (mem_pointer[tmp+3] & 0x000000ff));

  // Load main directory
  *dir_start=DIR_START_BLOCK;
  *dir_cont = 2;

  // Scan Main Directory
  for(i=0;i<MAX_NUM_OF_DIR_ENTRIES;i++) {
    for(j=0; j < EFE_SIZE ; j++) {
      EFE[i][j]=mem_pointer[DIR_START_BLOCK*BLOCK_SIZE + i * EFE_SIZE + j];
    }
  }

  //LoadDirBlocks(media_type,fd,DiskFAT,in,dir_start,dir_cont,EFE);

  // SUB-DIRS - Use the 'path' to 'change dir'...
  if(subdir_cnt >0) {
    for(i=0; i < subdir_cnt; i++) {
      j=DirPath[i];
      if (EFE[j][1] != 2) {
		EEXIT((stderr,"ERROR: Index '%d' is not a directory! \r\n\r\n",j));
      }

      strncpy(parent_dir_name, EFE[j]+2, 12);
      *dir_cont  =(unsigned int)  ((EFE[j][16] << 8) + EFE[j][17]);
      *dir_start =(unsigned long) ((EFE[j][18] << 24) + (EFE[j][19] << 16)
				   +(EFE[j][20] << 8 ) +  EFE[j][21]);

      LoadDirBlocks(*media_type,fd,*DiskFAT,in,*dir_start,*dir_cont,EFE);
    }

  } else {
    // if parent is root dir, set parent_name to 'ROOT'
    strncpy(parent_dir_name,"ROOT        ", 12);
  }

}

////////////////////////////////////////////////////
// CheckMedia
// ----------
// -Get info about used media and check the filesystem
//  structure

void CheckMedia(char media_type, FD_HANDLE fd, int file, int check_level)
{
  unsigned long i,j,count,used_blks;
  unsigned char buffer[BLOCK_SIZE],*root_dir;
  unsigned long total_blks,free_blks;
  unsigned long file_size;


  //Get File/Device info
#ifdef __CYGWIN__
  if((media_type=='f') || (media_type=='s')) {
#else // Linux and macOS
  if(media_type=='f') {
#endif
    // FILE ACCESS
    if((file_size=lseek(file,0,SEEK_END)) == -1) {
      perror("lseek");
      exit(ERR);
    }
  } else {
    // DISK ACCESS
#ifdef __CYGWIN__
    // How to do this in Windows!?

#else // Linux and macOS
    if((file_size=lseek(fd,0,SEEK_END)) == -1) {
      perror("lseek");
      exit(ERR);
    }
#endif

  }

  printf("\r\nFile/Device size: %ld bytes (%ld blocks) \r\n\r\n",file_size,file_size/BLOCK_SIZE);

  //ID Block

  ReadBlocks(media_type,fd,file,ID_BLOCK,1,buffer);

  printf("\r\nID BLOCK\r\n");
  printf("========\r\n\r\n");

  printf("Device type            : %d(%x)\r\n"  ,buffer[0],buffer[0]);
  printf("Rem. Media Device type : %d(%x)\r\n"  ,buffer[1],buffer[1]);
  printf("Std. Version #         : %d(%x)\r\n"  ,buffer[2],buffer[2]);
  printf("SCSI (?)               : %d(%x)\r\n"  ,buffer[3],buffer[3]);
  printf("Number of Sectors      : %d(%x%x)\r\n",(buffer[4]*256+buffer[5]),buffer[4],buffer[5]);
  printf("Number of Heads        : %d(%x%x)\r\n",(buffer[6]*256+buffer[7]),buffer[6],buffer[7]);
  printf("Number of Tracks       : %d(%x%x)\r\n",(buffer[8]*256+buffer[9]),buffer[8],buffer[9]);
  printf("Bytes per Block (512)  : %d(%x%x)\r\n",(buffer[12]*256+buffer[13]),buffer[12],buffer[13]);

  total_blks = ((buffer[14] << 24) +
		(buffer[15] << 16) +
		(buffer[16] << 8 ) +
		(buffer[17] & 0x000000ff));
  printf("Total Blocks           : %ld(%x%x%x%x) (%ld Bytes = %ld KBytes = %ld MBytes)\r\n",
	 total_blks,
	 buffer[14],buffer[15],buffer[16],buffer[17],
	 total_blks*512,total_blks*512/1024,total_blks*512/1024/1024);

  printf("SCSI Medium type       : %d(%x)\r\n"  ,buffer[18],buffer[18]);
  printf("SCSI Density Code      : %d(%x)\r\n"  ,buffer[19],buffer[19]);

  printf("DISK LABEL             : \"%c%c%c%c%c%c%c\" \r\n",buffer[31],buffer[32],buffer[33],
	 buffer[34],buffer[35],buffer[36],buffer[37]);

  printf("End of ID Block(\"ID\")  : \"%c%c\"\r\n",buffer[38],buffer[39]);

  //OS Block
  ReadBlocks(media_type,fd,file,OS_BLOCK,1,buffer);

  printf("\r\nOS BLOCK\r\n");
  printf("========\r\n\r\n");

  free_blks = ((buffer[0] << 24) +
	       (buffer[1] << 16) +
	       (buffer[2] << 8 ) +
	       (buffer[3] & 0x000000ff));

  printf("Free Blocks            : %ld(%x%x%x%x)\r\n",free_blks,
	 buffer[0],buffer[1],buffer[2],buffer[3]);

  printf("Disk OS Version        : %d.%d(%x.%x)\r\n"  ,buffer[4],buffer[5],buffer[4],buffer[5]);
  printf("ROM  OS Version        : %d.%d(%x.%x)\r\n"  ,buffer[6],buffer[7],buffer[6],buffer[7]);

  printf("End of OS Block(\"OS\")  : \"%c%c\"\r\n",buffer[28],buffer[29]);

  printf("\r\nOther Blocks\r\n");
  printf("============\r\n\r\n");

  count=0;
  used_blks=0;

  ReadBlocks(media_type,fd,file,DIR_END_BLOCK,1,buffer);

  printf("Root DirBlocks    : ");
  if(buffer[510]=='D' && buffer[511]=='R')
    printf("OK\r\n");
  else
    printf("NOT OK - DISK/FILE is corrupted!\r\n");

  for(i=FAT_START_BLOCK;;i++) {

    ReadBlocks(media_type,fd,file,i,1,buffer);

    //Check if valid FAT BLOCK
    if(buffer[510]!='F' || buffer[511]!='B')
      break;

    // Count used blocks by looking for all entries which are not '000' coded
	// within the FAT. Each FAT entries is three bytes, and last two bytes of
	// FAT block must be "FB", so only 510 bytes (170 entries) need to be
	// checked per FAT block.
    for(j=2;j<510;j=j+3) {

      if( !((buffer[j] == 0) && (buffer[j-1] ==0) && (buffer[j-2]==0)))
	  // if FAT entry is not '000' then that block has to store data
	  used_blks++;

    }
    count++;
  }

  printf("Num. of FAT blocks: %ld\r\n",count);
  printf("FAT entries       : %ld  => ",FAT_ENTRIES_PER_BLK*count);
  if((FAT_ENTRIES_PER_BLK*count) >= total_blks)
    printf("OK\r\n");
  else
    printf("FAT corrupted!! Not enough FAT tables!\r\n");

  printf("Used Blocks in FAT: %ld  => ",used_blks);
  if( (total_blks - (used_blks+free_blks)) == 0)
    printf("OK\r\n");
  else
    printf("FAT corrupted!! Used blocks should be %ld\r\n",total_blks - free_blks);

  printf("\r\n");

  // If higher check_level, display also root dir structure
  if(check_level > 0) {
    // Directory structure info
    printf("\r\nROOT DIR:\r\n");
    printf("=========\r\n");

    root_dir=(unsigned char *) malloc(BLOCK_SIZE*2);

    ReadBlocks(media_type,fd,file,DIR_START_BLOCK,2,root_dir);

    // Scan Directory
    for(i=0;i<MAX_NUM_OF_DIR_ENTRIES;i++) {
      char name[13];
      printf("%3ld:",i);
      for(j=0; j < EFE_SIZE ; j++) {
	printf("%02x ",root_dir[i * EFE_SIZE+j]);
      }
      printf("\r\n");
      strncpy(name, &root_dir[i * EFE_SIZE+2],12);
      name[12]='\0';

      printf("    Type:%2d, Name:%12s, Size:%ld, Cont:%ld, Start:%ld \r\n\r\n",
	     root_dir[i * EFE_SIZE+1],
	     name,
	     (long) root_dir[i * EFE_SIZE+14]*256+root_dir[i * EFE_SIZE+15],
	     (long) root_dir[i * EFE_SIZE+16]*256+root_dir[i * EFE_SIZE+17],
	     (long) root_dir[i * EFE_SIZE+18]*256*256*256+root_dir[i * EFE_SIZE+19]*256*256 +
	     root_dir[i * EFE_SIZE+20]*256+root_dir[i * EFE_SIZE+21]
	     );
    }
    free(root_dir);
  }

}

////////////////////////////////////////////////////
// Confirm
// -------
// -Asks if user wants to proceed

void Confirm()
{
  char answer;

  printf("\r\nThis operation will DESTROY everything in the TARGET medium! \r\n\r\n");
  printf("Are you *ABSOLUTELY* sure you want to proceed? (y/n) ");
  scanf("%c",&answer);

  if((answer == 'y') || (answer == 'Y'))
    printf("\r\n");
  else {
    printf("Operation aborted! \r\n\r\n");
    exit(OK);
  }
}

///////////////////////
// ImageCopy
// ----------
// -Copy image file to another one. Use to copy
// for ex. CD-ROM to HD etc.

int ImageCopy(char *source_file_name, char *target_file_name)
{
	//FILE *source, *target;
	unsigned int i=0;
	unsigned long source_file_size, target_file_size;
	unsigned char buffer[IMAGE_COPY_BUFFER_BLOCKS*BLOCK_SIZE];

	int source,target;
  // these values need to be larger than a signed int can hold!
	signed long read_bytes, write_bytes;

	printf("\r\n");

	// Open source file and get file size
	if( (source=open(source_file_name,O_RDONLY | O_BINARY)) < 0) {
      perror("open:");
      EEXIT((stderr,"ERROR: Couldn't open source file '%s'. \r\n",source_file_name));
	}

	source_file_size=lseek(source, 0, SEEK_END);

	// Check validity of source file
	if(source_file_size == 0)
      EEXIT((stderr,"ERROR: Source file '%s' is empty. \r\n",source_file_name));
	if((source_file_size % BLOCK_SIZE) != 0) {
	  EEXIT((stderr,"Source size has to be a multiple of block size %d! \r\n",BLOCK_SIZE));
	  exit(ERR);
	}

	if((target=open(target_file_name,O_RDWR | O_BINARY)) < 0) {
		if((target=open(target_file_name,O_RDWR | O_CREAT | O_BINARY, FILE_RIGHTS)) < 0) {	 // was S_IRWXU (0700)
			perror("open:");
			EEXIT((stderr,"ERROR: Couldn't open target file '%s'. \r\n",target_file_name));
		}
	    //printf("Creating new file '%s'\r\n", target_file_name);
    }

	target_file_size=lseek(target,0,SEEK_END);

	if(target_file_size == 0) {
		printf("Creating target file %s \r\n",target_file_name);
	} else {
		if(source_file_size > target_file_size) {
		EEXIT((stderr,"ERROR: Couldn't fit! \r\nSource '%s' is BIGGER that target '%s'. \r\n\r\nSource size: %ld Bytes, target size %ld Bytes \r\n\r\n",
			source_file_name, target_file_name,source_file_size,target_file_size));

		}
	}

	//printf("s:%ld,t:%ld\r\n",source_file_size,target_file_size);

	if(lseek(source,0,SEEK_SET) < 0) {
		perror("seek");
		return(ERR);
	}

	if(lseek(target,0,SEEK_SET) < 0) {
		perror("seek");
		return(ERR);
	}

	// Do copy in big chunks...
	do {
		read_bytes=read(source,buffer,IMAGE_COPY_BUFFER_BLOCKS*BLOCK_SIZE);
    // for this comparison to work, read_bytes has to counter-intuitively
    // be unsigned to allow for negative state of errorlevel
		if(read_bytes < 0) {
			perror("read");
			return(ERR);
		}
		// if last read was "full" read, but get all the data left, next read is 0
		if(read_bytes == 0) break;

    // calculate proper percentage in integer form
    unsigned int copyPercentage = ((100*i++) / ((source_file_size / BLOCK_SIZE) / IMAGE_COPY_BUFFER_BLOCKS));
    printf("\rCopying image file... %d%% completed",copyPercentage);

		write_bytes=write(target,buffer,read_bytes);
    // for this comparison to work, write_bytes has to counter-intuitively
    // be unsigned to allow for negative state of errorlevel
		if(write_bytes< 0) {
			perror("write");
			return(ERR);
		}
	} while (read_bytes == (IMAGE_COPY_BUFFER_BLOCKS*BLOCK_SIZE));

	printf("\rImage copy from '%s' to '%s' done! Total %ld Bytes copied. \r\n",source_file_name,target_file_name,source_file_size);
	fflush(stdout);

	close(source);close(target);
	return(OK);
}


//##############################################################################
//############################### MAIN PROGRAM   ###############################
//##############################################################################

int main(int argc, char **argv)
{
  int in;

  unsigned char EFE[MAX_NUM_OF_DIR_ENTRIES][EFE_SIZE];
  unsigned char *DiskFAT,*DiskHdr, *mem_pointer;
  char DiskLabel[DISK_LABEL_SIZE];

  unsigned int DirPath[MAX_DIR_DEPTH], subdir_cnt;
  unsigned int total_blks, free_blks, fat_blks;
  unsigned int dir_start, dir_cont, start_idx;

  unsigned long i,j;

  char c, media_type, image_type, process_EFE[MAX_NUM_OF_DIR_ENTRIES], in_file[FILENAME_MAX];
  char mkdir_name[12], parent_dir_name[12];
  char format_arg;
  FD_HANDLE fd;
  unsigned int trk_size, nsect;
  int mode, printmode;
  int check_level, confirm_operation;

  //
  // Initialize variables
  //
  mode = NONE; subdir_cnt = 0; j = 0; image_type= -1; printmode = HUMAN_READABLE;
  //
  trk_size =  0; media_type  = 0; fat_blks   = 0; in = 0;
  //
  DiskFAT = NULL; mem_pointer=NULL; start_idx = 1;
  // whether or not confirmation is needed on operations such as Format...
  // ..."quiet" mode silences the confirm operation prompt
  confirm_operation = 0;
  // generate default disk label
  strncpy(DiskLabel,DEFAULT_DISK_LABEL,DISK_LABEL_SIZE);
  //
  fd= (FD_HANDLE) NULL;

  // initialize an array which deals with GetEFE routine
  for(i=0;i < MAX_NUM_OF_DIR_ENTRIES; i++) process_EFE[i]=0;

  //printf("\r\n");

  // Get options and parameters
  while (1)
	{
		// parse command-line arguments
		// c = getopt(argc, argv, "Pj:b:srwf:g:p::e:d:m:itc:C::l:qI");
		   c = getopt(argc, argv, "Pj:b:srwf:g:p::e:d:m:itc:C::l:qID?");
		if (c == -1)
		{
			break;			// break the while loop if no arguments are supplied -- skips switch handling
		}

		switch (c)
		{
			case 'b':         // ** Bank Info **
			PrintBankInfo(optarg,printmode);
			//printf("%d,%s\r\n",printmode,optarg);
			exit(OK);
			break;
			case 'P':         // ** COMPUTER READABLE DIRLIST **
			printmode = COMPUTER_READABLE;
			break;
			case 's':	  // ** SPLIT EFE **
			SplitEFE(argv[2], argv[3], argc);
			exit(OK);
			break;
			case 'j':	  // ** JOIN EFEs **
			JoinEFEs(argc,argv);
			exit(OK);
			break;
			case 't':	  // ** TEST **
			//EEXIT((stderr,"ERROR: No test modes!\r\n"));
			mode =  TEST;
			break;

			case 'C':        // ** CHECK MEDIA **
			//printf("argv[optind=%d]=%s,argc=%d\r\n",optind,argv[optind],argc);
			GetMedia(argv[optind], argc,  &media_type, &image_type, &nsect, &trk_size, &fd, in_file, &in);
			if(optarg==NULL) check_level=0; else check_level=*optarg-'0';
			CheckMedia(media_type, fd, in, check_level);
			exit(OK);
			break;

			case 'c':	  // ** CONVERT **
			DoConversion(argv[2], argv[3], argc);
			exit(OK);
			break;

			case 'i':	  // ** INFO **
			if(FD_GetDiskType(&media_type,&nsect,&trk_size) == ERR) {
				EEXIT((stderr,"ERROR: Not an Ensoniq disk. \r\n       Please format the disk (-fe or -fa) and try again! \r\n\r\n"));
			}
			exit(OK);
			break;

			case 'I':        // ** IMAGE COPY ***
			if(confirm_operation ==0) Confirm();
			//printf("source=%s,target=%s\r\n",argv[optind],argv[optind+1]);
			ImageCopy(argv[optind],argv[optind+1]);
			exit(OK);
			break;

			case 'r':  	  // ** READ DISK to IMAGE **
			mode = READ;
			confirm_operation++;
			break;

			case 'w':  	  // ** WRITE DISK from IMAGE **
			mode = WRITE;
			confirm_operation++;
			break;

			case 'f':  	  // ** FORMAT DISK/IMAGE **
			mode=FORMAT;
			confirm_operation++;
			format_arg=optarg[0];
			break;

			case 'l':
			strncpy(DiskLabel,optarg,DISK_LABEL_SIZE);
			break;

			case 'g': 	  // ** Get EFEs **
			ParseEntry(optarg,process_EFE);
			mode=GET;
			break;

			case 'p': 	  // ** Put EFEs **
			if(optarg != NULL) {
				start_idx = atoi(optarg);
			}
			mode=PUT;
			break;

			case 'e': 	  // ** Erase EFEs **
			ParseEntry(optarg,process_EFE);
			mode=ERASE;
			break;

			case 'd': 	  // ** Directory **
			ParseDir(optarg, DirPath, &subdir_cnt);
			//printf("DirPath:%s\r\n",optarg);
			break;

			case 'D': 	  // ** Directory **
			mode=DIRLIST;
			break;

			case 'm': 	  // ** Make directory **
			mode=MKDIR;
			strncpy(mkdir_name, optarg,12);
			break;

			case 'q':        // Quiet mode -- suppress confirmation prompt
			confirm_operation--;
			break;

			case '?':		// usage help -- same as supplying no argument
			break;

			default:
			printf("DEFAULT\r\n");
			printf ("\r\n");
		}	// end switch
    }	// end while

  // if no command-argument (or '?') is given then display program usage help information
  if(mode == NONE) {
	ShowUsage();			// show help
	return(ERR);			// quit program with error code
  }

  if(mode == DIRLIST) {
	printf("Ensoniq EPS/ASR Directory and Disk Information \r\n");
  }

  if(mode == FORMAT) {
	// make sure user intends to actually format
    if(confirm_operation) Confirm();
	// if so then proceed to format routine
    FormatMedia(argv, argc, optind, format_arg, DiskLabel);
  }

  // If mode is anything other than disk read/write then GETMEDIA and GETINFO
  if((mode != WRITE) && (mode != READ)) {

    // Check if DISK or FILE access and get media parameters
#ifdef DEBUG
	printf("GETMEDIA\r\n");fflush(stdout);
#endif
    GetMedia(argv[optind], argc,  &media_type, &image_type,
	     &nsect, &trk_size, &fd, in_file, &in);
#ifdef DEBUG
	printf("media_type=%c\r\n",media_type);
#endif

    // GET DIR & MISC INFO
#ifdef DEBUG
	printf("GETINFO\r\n");fflush(stdout);
#endif
    GetInfo(&media_type, fd, &DiskFAT, &DiskHdr, in, EFE,
    	    &fat_blks, &free_blks, &total_blks, &dir_start, &dir_cont,
    	    parent_dir_name, subdir_cnt, DirPath, DiskLabel);

  } // end of GETMEDIA/GETINFO stage

  // Select operation mode (if any)
  // ==============================
  switch (mode)
    {
    case READ:    // Read/Write DISK
    case WRITE:
      if(confirm_operation) Confirm();
      FD_RW_Disk(argv[optind], mode);
      exit(OK);

    case GET:   // Get EFEs
      GetEFEs(media_type, fd, in, EFE, process_EFE, DiskFAT);
      break;

    case PUT:   // Put EFEs
#ifdef DEBUG
	  printf("PUTEFE\r\n");fflush(stdout);
#endif
      PutEFE(process_EFE, start_idx, EFE, media_type, image_type,
	     in_file, argv, optind,  argv[optind],
	     dir_start, dir_cont, total_blks, &free_blks, fat_blks,
	     fd, DiskFAT, DiskHdr, NULL, NULL);
      break;

    case ERASE: // Erase EFEs
      EraseEFEs(media_type, image_type, fd, DiskFAT, DiskHdr, in_file, argv[optind],
		EFE, process_EFE,
		fat_blks, &free_blks, dir_start, dir_cont);
      break;

    case MKDIR: // Make Dir
      MkDir(process_EFE, EFE, media_type, image_type,
	    in_file, argv[optind],
	    dir_start, dir_cont, parent_dir_name, total_blks,
	    &free_blks, fat_blks,
	    fd, DiskFAT, DiskHdr, mkdir_name);
      break;

    case TEST:
      printf("\r\nFAT:\r\n");
      for(i=0 ; i<total_blks; i++) {
	switch(GetFatEntry(media_type,DiskFAT,in,i)) {
	case 0:
	  printf(".");
	  break;
	case 1:
	  printf("E");
	  break;
	default:
	  printf("#");
	}

      }
      printf("\r\n");
      exit(0);

    }

  // Close file-pointers if needed
  if(in != 0) close(in);

  if(fd != (FD_HANDLE) NULL) {
    CloseFloppy(fd);
  }

#ifdef DEBUG
  printf("PRINTDIR\r\n");fflush(stdout);
#endif

  // Print the DirectoryList - Uses 'original' filename (not tmp :-)
  PrintDir(EFE, mode, process_EFE, argv[optind], media_type, DiskLabel,
	   free_blks, (total_blks - free_blks - fat_blks - 5),printmode);

  exit(OK);
}
