#include <stdio.h>
#include <stdint.h>
#include <dirent.h>
#include <sys/stat.h>
#include <pthread.h>
#include <stdlib.h>
#include <fcntl.h>
#include <string.h>
#include <limits.h>
#include <stdbool.h>
#include <unistd.h>

/*Josh's defines*/
#define ALPHABET_LEN 256
#define NOT_FOUND patlen
#define max(a, b) ((a < b) ? b : a)
int chars_compared;
//#define DEBUG




/*Chris defines*/
#define BLOOMSIZE 40000
int bloom[BLOOMSIZE];
char * term;
char cwd[PATH_MAX];
pthread_mutex_t lock;
//pthread_mutex_t sleeplock;
int LOOP;
void *dirLoop(void *);
void search(char * fName);
unsigned int PJWHash(const char* str, unsigned int length);
unsigned int JSHash(const char* str, unsigned int length);
unsigned int RSHash(const char* str, unsigned int length);
int checkHash(const char * str);
int insertHash(const char * str);
int insertCheckHash(const char * str);


/*Josh functions*/
void print_line(uint8_t *string, int pos, uint32_t patlen, uint32_t * linenum, uint8_t *filename){
  uint8_t * cpy_str = string;
  int offset = 0;
  cpy_str += pos; //move cpy_str pointer to point to the found string
  int j = 0;
  int z = 0;
  //index to an offset of -3 from the found term for pretty printing
  while(j < 3 && z < 30){
    if (cpy_str[offset] != '\0' && cpy_str[offset] != '\n' && cpy_str[offset] != '\t'){
      if (cpy_str[offset] == ' '){
	++j;
      }
      offset--;
      z++;
    }
    else{
      offset++;
      break;
    }
  }
  if (cpy_str[offset] == '\0' && cpy_str[offset] == '\n' && cpy_str[offset] == '\t')
    ++offset;
  cpy_str += offset;

  int i;
  j = 0;
  char buf[41];
  memset(buf, 0, sizeof(buf));
  char temp[2];
  temp[1] = '\0';
  while (j < 40){
    if(cpy_str[j] != '\n' && cpy_str[j] != '\0'){
      if (cpy_str[j] != '\t'){
	temp[0] = cpy_str[j];
	strcat(buf, temp);
	//snprintf(buf, 40, "%s%c", buf, cpy_str[j]);
      }
      if (cpy_str[j] == ' ')
	++i;
      ++j;
    }
    else
      break;
  }
  /*if (strlen(buf) < 2)
    return;*/
  printf("%s contains %s on line %d: %s", filename, term, *linenum, buf);
  printf("\n");
  return;
}

//The implementation of Booyer-Moore was copied from https://github.com/likejazz/boyer-moore-string-search and modified appropriately


// delta1 table: delta1[c] contains the distance between the last
// character of pat and the rightmost occurrence of c in pat.
// If c does not occur in pat, then delta1[c] = patlen.
// If c is at string[i] and c != pat[patlen-1], we can
// safely shift i over by delta1[c], which is the minimum distance
// needed to shift pat forward to get string[i] lined up
// with some character in pat.
// this algorithm runs in alphabet_len+patlen time.
void make_delta1(int *delta1, uint8_t *pat, int32_t patlen) {
  int i;
  #ifdef DEBUG
  int j;
  int delta1_chars[patlen];
  int max_chars = 0;
  bool is_matched = false;
  #endif

  for (i=0; i < ALPHABET_LEN; i++) {
    delta1[i] = NOT_FOUND;
  }
  for (i=0; i < patlen-1; i++) {
    delta1[pat[i]] = patlen-1 - i;
    #ifdef DEBUG
    is_matched = false;
    for (j=0; j <= max_chars; j++) {
      if (delta1_chars[j] == pat[i]) {
	is_matched = true;
      }
    }
    if (is_matched == false) {
      delta1_chars[max_chars] = pat[i];
      max_chars++;
    }
    #endif
  }
  #ifdef DEBUG
  int t;
  printf ("\n");
  for (t=0; t < max_chars; t++)
    printf("delta1[%c] = %d\n", delta1_chars[t], delta1[delta1_chars[t]]);
  printf("delta1[other] = %d\n", NOT_FOUND);
  #endif
}

// true if the suffix of word starting from word[pos] is a prefix
// of word
int is_prefix(uint8_t *word, int wordlen, int pos) {
  int i;
  int suffixlen = wordlen - pos;

  for (i=0; i < suffixlen; i++) {
    if (word[i] != word[pos+i]) {
      return 0;
    }
  }
  return 1;
}

// length of the longest suffix of word ending on word[pos].
// suffix_length("dddbcabc", 8, 4) = 2
int suffix_length(uint8_t *word, int wordlen, int pos) {
  int i;
  // increment suffix length i to the first mismatch or beginning
  // of the word
  for (i = 0; (word[pos-i] == word[wordlen-1-i]) && (i < pos); i++);
  return i;
}

// delta2 table: given a mismatch at pat[pos], we want to align
// with the next possible full match could be based on what we
// know about pat[pos+1] to pat[patlen-1].
//
// In case 1:
// pat[pos+1] to pat[patlen-1] does not occur elsewhere in pat,
// the next plausible match starts at or after the mismatch.
// If, within the substring pat[pos+1 .. patlen-1], lies a prefix
// of pat, the next plausible match is here (if there are multiple
// prefixes in the substring, pick the longest). Otherwise, the
// next plausible match starts past the character aligned with
// pat[patlen-1].
//
// In case 2:
// pat[pos+1] to pat[patlen-1] does occur elsewhere in pat. The
// mismatch tells us that we are not looking at the end of a match.
// We may, however, be looking at the middle of a match.
//
// The first loop, which takes care of case 1, is analogous to
// the KMP table, adapted for a 'backwards' scan order with the
// additional restriction that the substrings it considers as
// potential prefixes are all suffixes. In the worst case scenario
// pat consists of the same letter repeated, so every suffix is
// a prefix. This loop alone is not sufficient, however:
// Suppose that pat is "ABYXCDEYX", and text is ".....ABYXCDEYX".
// We will match X, Y, and find B != E. There is no prefix of pat
// in the suffix "YX", so the first loop tells us to skip forward
// by 9 characters.
// Although superficially similar to the KMP table, the KMP table
// relies on information about the beginning of the partial match
// that the BM algorithm does not have.
//
// The second loop addresses case 2. Since suffix_length may not be
// unique, we want to take the minimum value, which will tell us
// how far away the closest potential match is.
void make_delta2(int *delta2, uint8_t *pat, int32_t patlen) {
  int p;
  int last_prefix_index = 1;

  // first loop, prefix pattern
  for (p=patlen-1; p>=0; p--) {
    if (is_prefix(pat, patlen, p+1)) {
      last_prefix_index = p+1;
    }
    delta2[p] = (patlen-1 - p) + last_prefix_index;
  }

  // this is overly cautious, but will not produce anything wrong
  // second loop, suffix pattern
  for (p=0; p < patlen-1; p++) {
    int slen = suffix_length(pat, patlen, p);
    if (pat[p - slen] != pat[patlen-1 - slen]) {
      delta2[patlen-1 - slen] = patlen-1 - p + slen;
    }
  }
  #ifdef DEBUG
  int t;
  printf ("\n");
  for (t=0; t < patlen; t++) {
    printf("delta2[%c]: %d\n", pat[t], delta2[t]);
  }
  #endif
  return;
}

uint32_t boyer_moore (uint8_t *string, uint32_t stringlen, uint8_t *pat, uint32_t patlen, uint32_t * linenum, uint8_t *filename) {
  int i;
  int delta1[ALPHABET_LEN];
  int *delta2 = malloc(patlen * sizeof(int));
  make_delta1(delta1, pat, patlen);
  make_delta2(delta2, pat, patlen);
  int n_shifts = 0;
  chars_compared = 0;
  #ifdef DEBUG
  printf ("\n");
  #endif
  i = patlen-1;
  while (i < stringlen) {
    int j = patlen-1;
    while (j >= 0 && (string[i] == pat[j])) {
		//printf("SecondWhile\n");fflush(stdout);
      --i;
      --j;
      chars_compared++;
    }
	//printf("LastWhile\n");fflush(stdout);
    /*if (string[i] == '\n')
     *linenum++;*/
    //Here is where Boyer returns the position
    //TODO: make this so that boyer keeps going and instead call another function to print out the surrounding text to the screen
    if (j < 0) {
      print_line(string, i+1, patlen, linenum, filename);
      //printf("%c %d\n", string[i], i);
      chars_compared += patlen;
      i += patlen + 1;
      continue;
      //free(delta2);
      //return (uint32_t) i+1;
    }
    chars_compared++;
    #ifdef DEBUG
    n_shifts++;

    if (delta1[string[i]] > delta2[j]) {
      printf("shift #%d, using delta1, shifting by %d\n", n_shifts, delta1[string[i]]);
    } else {
      printf("shift #%d, using delta2, shifting by %d\n", n_shifts, delta2[j]);
    }
    #endif

    i += max(delta1[string[i]], delta2[j]);
  }

  free(delta2);
  return 0;
}

void test(uint8_t *string, uint8_t *pat) {
  uint32_t linenum = 0;
  uint8_t buffer[4096];
  FILE *fp;
  //printf("-------------------------------------------------------\n");
  //printf("Looking for '%s' in '%s':\n", pat, string);

  //TODO: open filename for reading and start to fill a string buffer
  /* opening file for reading */
  fp = fopen((char*)string , "r");
  if(fp == NULL) {
    perror("Error opening file");
    return;
  }
  while( fgets(buffer, 4096, fp)!=NULL ) {
    /* writing content to stdout */
	//printf("FirstWhile\n");fflush(stdout);
    uint32_t pos = boyer_moore(buffer, strlen(buffer), pat, strlen(pat), &linenum, string);
#ifdef DEBUG
    printf("\n");
#endif
    /*if (pos == 0 && chars_compared != strlen(pat))
      printf("Not Found - ");
    else
    printf("Found at position %u - ", pos);*/
   // printf("%d chars compared.\n", chars_compared);
    ++linenum;
  }
  fclose(fp);
  return;
}





/*Chris Functions*/






struct passVal
{
	char Dirname[900];
	int children;
};

int main(int argc, char *argv[])
{
	int i;
	pthread_t  wait[1];
	memset(bloom,0,sizeof(bloom));
	if(argc != 2)
	{
		printf("Usage: grepR.x searchTerm\n");
		return -1;
	}
	term = argv[1];
	
	for(i = 0; i < BLOOMSIZE; ++i)
	{
		bloom[i] = 0;
	}
	LOOP = 1;
	getcwd(cwd, sizeof(cwd));
	//create thread on this
	pthread_mutex_init(&lock,NULL);
	//pthread_mutex_init(&sleeplock,NULL);
	insertHash(cwd);
	//pthread_mutex_lock(&sleeplock);
	pthread_create(&wait[0], NULL, dirLoop, NULL);
	//wait here
	//printf("Waiting at join\n");fflush(stdout);
	while(LOOP != 0);

	//printf("At mutex wait\n");fflush(stdout);
	pthread_mutex_destroy(&lock);
	//pthread_mutex_destroy(&sleeplock);
	
	return 0;
	
}

/*Hash from Robert Sedgwichs Algorithms in C book*/
unsigned int RSHash(const char* str, unsigned int length)
{
   unsigned int b    = 378551;
   unsigned int a    = 63689;
   unsigned int hash = 0;
   unsigned int i    = 0;

   for (i = 0; i < length; ++str, ++i)
   {
      hash = hash * a + (*str);
      a    = a * b;
   }

   return hash;
}

/*Hash written by Justin Sobel*/
unsigned int JSHash(const char* str, unsigned int length)
{
   unsigned int hash = 1315423911;
   unsigned int i    = 0;

   for (i = 0; i < length; ++str, ++i)
   {
      hash ^= ((hash << 5) + (*str) + (hash >> 2));
   }

   return hash;
}

/*Hash by Peter J. Weinberger of AT&T Bell Labs*/
unsigned int PJWHash(const char* str, unsigned int length)
{
   const unsigned int BitsInUnsignedInt = (unsigned int)(sizeof(unsigned int) * 8);
   const unsigned int ThreeQuarters     = (unsigned int)((BitsInUnsignedInt  * 3) / 4);
   const unsigned int OneEighth         = (unsigned int)(BitsInUnsignedInt / 8);
   const unsigned int HighBits          =
                      (unsigned int)(0xFFFFFFFF) << (BitsInUnsignedInt - OneEighth);
   unsigned int hash = 0;
   unsigned int test = 0;
   unsigned int i    = 0;

   for (i = 0; i < length; ++str, ++i)
   {
      hash = (hash << OneEighth) + (*str);

      if ((test = hash & HighBits) != 0)
      {
         hash = (( hash ^ (test >> ThreeQuarters)) & (~HighBits));
      }
   }

   return hash;
}

int checkHash(const char * str)
{
	unsigned long hashReturn;
	
	hashReturn = RSHash(str, strlen(str));
	if((bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] | 1 << ((hashReturn%BLOOMSIZE)%sizeof(int))) == 0) return 0;
	hashReturn = JSHash(str, strlen(str));
	if((bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] & 1 << ((hashReturn%BLOOMSIZE)%sizeof(int))) == 0) return 0;
	hashReturn = PJWHash(str, strlen(str));
	if((bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] & 1 << ((hashReturn%BLOOMSIZE)%sizeof(int))) == 0) return 0;
	return 1;
}

int insertCheckHash(const char * str)
{
	unsigned long hashReturn;
	int inside;
	inside = 0;
	hashReturn = RSHash(str, strlen(str));
	if((bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] | 1 << ((hashReturn%BLOOMSIZE)%sizeof(int))) == 0)
	{
		inside = 1;
		bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] |= 1 << ((hashReturn%BLOOMSIZE)%sizeof(int));
	}
	hashReturn = JSHash(str, strlen(str));
	if((bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] & 1 << ((hashReturn%BLOOMSIZE)%sizeof(int))) == 0)
	{
		inside = 1;
		bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] |= 1 << ((hashReturn%BLOOMSIZE)%sizeof(int));
	}
	hashReturn = PJWHash(str, strlen(str));
	if((bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] & 1 << ((hashReturn%BLOOMSIZE)%sizeof(int))) == 0)
	{
		inside = 1;
		bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] |= 1 << ((hashReturn%BLOOMSIZE)%sizeof(int));
	}
	//printf("inside: %d\n",inside);
	return inside;
}

int insertHash(const char * str)
{
	unsigned long hashReturn;
	hashReturn = RSHash(str, strlen(str));
	bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] |= 1 << ((hashReturn%BLOOMSIZE)%sizeof(int));
	hashReturn = JSHash(str, strlen(str));
	bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] |= 1 << ((hashReturn%BLOOMSIZE)%sizeof(int));
	hashReturn = PJWHash(str, strlen(str));
	bloom[((hashReturn%BLOOMSIZE)/sizeof(int))] |= 1 << ((hashReturn%BLOOMSIZE)%sizeof(int));
}

void *dirLoop(void * Dirname)
{
	struct dirent *dirList;
	struct stat statistics;
	pthread_t  waitList[900];
	char ciwd[4000];
	char tempDirname[4000];
	int nul;
	DIR * curDir;
	int  list;
	int i;
	int dirfd;
	char link[4000];
	int *Junk;
	list = 0;
	pthread_detach(pthread_self());
	if(Dirname == NULL)
	{nul = 1;}
	else
	{nul = 0;}
	
	if(nul == 0)
	{
		//printf("Copying: %s\n", (char *) Dirname);
		strcpy(tempDirname,(char *)Dirname);
		if (readlink(tempDirname, link, sizeof(link)) != -1)
		{
			if(link[0] != '/')
			{
				realpath(link, tempDirname);
				//printf("really going to: %s\n",tempDirname);
				dirLoop(tempDirname); 
				pthread_exit((void*)1);
			}
			else
			{
				//printf("going to: %s\n",link);
				dirLoop(link); 
				pthread_exit((void*)1);
			}
		}
		if(insertCheckHash(tempDirname) == 0)
		{
			//printf("%s already found\n",tempDirname);
			--LOOP;
			pthread_mutex_unlock(&lock);
			pthread_exit((void*)1);
		}
		else
			pthread_mutex_unlock(&lock);
	}	
	
	
		// printf("Dirname: %s\n", (char *) Dirname);fflush(stdout);

	if(nul == 1)
	{
	//	printf("FirstTime :\n");fflush(stdout);
		if((curDir = opendir(cwd)) == NULL) pthread_exit(NULL);
	}
	else
	{ 
		//printf("Nest : %s\n", tempDirname);fflush(stdout);
		
		if((curDir = opendir(tempDirname)) == NULL) //this is for if its a file
		{//search((char *)Dirname);
			
			//printf("PreFile: %s\n",(char *)Dirname);fflush(stdout);
			
			
			
			test((uint8_t*)tempDirname, (uint8_t*)term);
			//printf("%s\n", tempDirname);
			pthread_mutex_lock(&lock);
			--LOOP;
			pthread_mutex_unlock(&lock);
			pthread_exit((void*)1);
		}
		//printf("HHHDir : %s\n", (char *)Dirname); fflush(stdout);
	}
	
	while((dirList = readdir(curDir)) != NULL)
	{
		stat(dirList->d_name,&statistics);
		//printf("%s: %s\n",(char *)Dirname,dirList->d_name);fflush(stdout);

		if(dirList->d_name[0] != '.')
		{
			pthread_mutex_lock(&lock);
			//printf("Dir: %s\n",dirList->d_name);
			if(nul ==0)
				strcpy(ciwd,tempDirname);
			else
				strncpy(ciwd,cwd,sizeof(cwd));
			//if(nul == 0)
			//	{printf("ciwd: %s %s\n",ciwd,tempDirname);fflush(stdout);}
			//else
			//	{printf("else ciwd: %s\n",ciwd);fflush(stdout);}
			strcat(ciwd,"/");
			strncat(ciwd,dirList->d_name,sizeof(dirList->d_name));
			//printf("ciwd: %s\n",ciwd);fflush(stdout);
			//dirLoop(ciwd);
			//printf("list: %d %s\n",list,ciwd);fflush(stdout);
			++list;
			//{printf("ciwd: %s %s %d\n",ciwd,tempDirname, list);fflush(stdout);}
			++LOOP;
			pthread_create(&(waitList[list]), NULL, dirLoop, (void *) ciwd);
			//printf("Pthreadmade\n");fflush(stdout);
			//pthread_join(waitList[list], NULL);
			
			
		}
		
//else if(S_ISLNK(statistics.st_mode)) printf("l\n");
	//	else printf("?\n");
		
	}
	//printf("LINK: %d\n", list);fflush(stdout);
	
	//for(i = 1; i < list+1; ++i)
	//{
		
	//	printf("joining %d\n",i); fflush(stdout);
	//	pthread_join(waitList[i], (void**)&Junk);
	//	printf("joined %d\n",i); fflush(stdout);
	//}
	pthread_mutex_lock(&lock);
	--LOOP;
	pthread_mutex_unlock(&lock);
	//pthread_mutex_lock(&sleeplock);
	pthread_exit(NULL);
}


void search(char * fName)
{
	char link[900];
	if (readlink(fName, link, sizeof(link)) != -1) {dirLoop(link); return;}
	//printf("File: %s\n", fName);fflush(stdout);
	return;
}







