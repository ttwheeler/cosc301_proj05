#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include "bootsect.h"
#include "bpb.h"
#include "direntry.h"
#include "fat.h"
#include "dos.h"

/*
 *Zach Schneiweiss and Tom Wheeler
*/
void usage(char *progname) {
    fprintf(stderr, "usage: %s <imagename>\n", progname);
    exit(1);
}

void print_indent(int indent)
{
    int i;
    for(i=0;i<indent*4;i++) printf(" ");
}
/* write the values into a directory entry */
void write_dirent(struct direntry *dirent, char *filename, 
		  uint16_t start_cluster, uint32_t size)
{
    char *p, *p2;
    char *uppername;
    int len, i;

    /* clean out anything old that used to be here */
    memset(dirent, 0, sizeof(struct direntry));

    /* extract just the filename part */
    uppername = strdup(filename);
    p2 = uppername;
    for (i = 0; i < strlen(filename); i++) 
    {
	if (p2[i] == '/' || p2[i] == '\\') 
	{
	    uppername = p2+i+1;
	}
    }

    /* convert filename to upper case */
    for (i = 0; i < strlen(uppername); i++) 
    {
	uppername[i] = toupper(uppername[i]);
    }

    /* set the file name and extension */
    memset(dirent->deName, ' ', 8);
    p = strchr(uppername, '.');
    memcpy(dirent->deExtension, "___", 3);
    if (p == NULL) 
    {
	fprintf(stderr, "No filename extension given - defaulting to .___\n");
    }
    else 
    {
	*p = '\0';
	p++;
	len = strlen(p);
	if (len > 3) len = 3;
	memcpy(dirent->deExtension, p, len);
    }

    if (strlen(uppername)>8) 
    {
	uppername[8]='\0';
    }
    memcpy(dirent->deName, uppername, strlen(uppername));
    free(p2);

    /* set the attributes and file size */
    dirent->deAttributes = ATTR_NORMAL;
    putushort(dirent->deStartCluster, start_cluster);
    putulong(dirent->deFileSize, size);
}
/* create_dirent finds a free slot in the directory, and write the
   directory entry */
void create_dirent(struct direntry *dirent, char *filename, 
		   uint16_t start_cluster, uint32_t size,
		   uint8_t *image_buf, struct bpb33* bpb)
{
    while (1) 
    {
	if (dirent->deName[0] == SLOT_EMPTY) 
	{
	    /* we found an empty slot at the end of the directory */
	    write_dirent(dirent, filename, start_cluster, size);
	    dirent++;

	    /* make sure the next dirent is set to be empty, just in
	       case it wasn't before */
	    memset((uint8_t*)dirent, 0, sizeof(struct direntry));
	    dirent->deName[0] = SLOT_EMPTY;
	    return;
	}

	if (dirent->deName[0] == SLOT_DELETED) 
	{
	    /* we found a deleted entry - we can just overwrite it */
	    write_dirent(dirent, filename, start_cluster, size);
	    return;
	}
	dirent++;
    }
}

uint32_t getClustSize(uint16_t start,uint8_t *image_buf, struct bpb33* bpb,uint16_t reff[],int indent)
{
    int j=0;
    while(reff[j]!=0)j++;
    reff[j]=start;//Put start in the referenced cluster array;
    int clusts=0;
    uint16_t tmpClust=start;
    reff[j+1]=tmpClust;
    while(!(is_end_of_file(tmpClust)))
    {
        if(get_fat_entry(tmpClust,image_buf,bpb)==(FAT12_MASK&CLUST_BAD))
        {
            uint16_t tmpNext=get_fat_entry(tmpClust,image_buf,bpb);
            print_indent(indent);
            printf("Found bad cluster at %u!\n",get_fat_entry(tmpNext,image_buf,bpb));
            set_fat_entry(tmpClust,(FAT12_MASK&CLUST_EOFS),image_buf,bpb);
            set_fat_entry(tmpNext,(FAT12_MASK&CLUST_FREE),image_buf,bpb);
            //Mark previous as EOF, then free current
        }
        j=0;
        while(reff[j]!=0)j++;
        reff[j]=tmpClust;//Add next cluster to referenced cluster array
        tmpClust=get_fat_entry(tmpClust,image_buf,bpb);
        clusts++;
    }
    return (clusts*(bpb->bpbBytesPerSec)*(bpb->bpbSecPerClust));
}

void truncateData(struct direntry *dirent,struct bpb33* bpb,uint8_t *image_buf)
{
    uint32_t metaSize=getulong(dirent->deFileSize);
    uint16_t clustSize=(bpb->bpbBytesPerSec*bpb->bpbSecPerClust);
    uint32_t numClusts;
    if((metaSize%clustSize)==0)numClusts=metaSize/clustSize;
    else numClusts=(metaSize/clustSize)+1;//Compensate for truncated division

    uint16_t newEOF=getushort(dirent->deStartCluster);//tmpClust holds first cluster
    for(int i=1;i<numClusts;i++) newEOF=get_fat_entry(newEOF,image_buf,bpb);
    uint16_t tmpClust=get_fat_entry(newEOF,image_buf,bpb);
    uint16_t tmpTwoClust;
    //Now iterate through remaining entries to free them
    while(!is_end_of_file(tmpClust))
    {
        tmpTwoClust=tmpClust;
        tmpClust=get_fat_entry(tmpClust,image_buf,bpb);
        set_fat_entry(tmpTwoClust,FAT12_MASK&CLUST_FREE,image_buf,bpb);
    }
    set_fat_entry(newEOF,(FAT12_MASK&CLUST_EOFS),image_buf,bpb);
}

//Prints and fixes metadata inconsitency problems, iterates through directory
uint16_t metaFix(struct direntry *dirent, int indent,uint8_t *image_buf,struct bpb33* bpb,uint16_t *reff)
{
    uint16_t followclust = 0;

    int i;
    char name[9];
    char extension[4];
    uint32_t metaSize;
    uint16_t file_cluster;
    name[8] = ' ';
    extension[3] = ' ';
    memcpy(name, &(dirent->deName[0]), 8);
    memcpy(extension, dirent->deExtension, 3);
    if (name[0] == SLOT_EMPTY)//Slot has never been used
    {
	return followclust;
    }
    if (((uint8_t)name[0]) == SLOT_DELETED)//Slot has been deleted
    {
	return followclust;
    }
    if (((uint8_t)name[0]) == 0x2E)//Dot entry (. or ..), skip it
    {
        return followclust;
    }
    for (i = 8; i > 0; i--)//Removes spaces from name
    {
	if (name[i] == ' ') name[i] = '\0';
	else break;
    }
    for (i = 3; i > 0; i--)//Removes spaces from extensions
    {
	if (extension[i] == ' ') extension[i] = '\0';
	else break;
    }
    if ((dirent->deAttributes & ATTR_WIN95LFN) == ATTR_WIN95LFN)
    {
	// ignore any long file name extension entries
	// printf("Win95 long-filename entry seq 0x%0x\n", dirent->deName[0]);
    }
    else if ((dirent->deAttributes & ATTR_VOLUME) != 0)//It is a volume 
    {
        printf("Volume: %s\n", name);
    }
    else if ((dirent->deAttributes & ATTR_DIRECTORY) != 0)//It is a directory, not file
    {
	if ((dirent->deAttributes & ATTR_HIDDEN) != ATTR_HIDDEN)
        {
            print_indent(indent);
            printf("%s/ (directory)\n",name);
            file_cluster = getushort(dirent->deStartCluster);
            int j=0;
            while(reff[j]!=0)j++;
            reff[j]=file_cluster;//Add cluster to referenced clusters array
            followclust = file_cluster;
        }
    }
    else//It is a regular file
    {
        //First check for metadata inconsistencies
	metaSize = getulong(dirent->deFileSize);//Size according to directory entry
        uint16_t start=getushort(dirent->deStartCluster);//Start cluster for file
        uint32_t clustSize=getClustSize(start,image_buf,bpb,reff,indent);
        //clustSize holds size according cluster chain
        uint32_t minSize=clustSize-511;//Minimum possible size
        if(metaSize>clustSize)
        {//This works
            print_indent(indent);
            printf("%s.%s has metadata/FAT chain inconsistencies! Updating metadata\n",name,extension);
            putulong(dirent->deFileSize,clustSize);//Metadata is too small, update
        }
        else if(metaSize<minSize)
        {
            print_indent(indent);
            printf("%s.%s has metadata/FAT chain inconsistencies! Truncating chain\n",name,extension);
            truncateData(dirent,bpb,image_buf);
        }
    }
    return followclust;
}

//Follows a directory, allowing recursive printing/fixing
void follow_dir(uint16_t cluster, int indent,uint8_t *image_buf, struct bpb33* bpb,uint16_t *reff)
{
    while (is_valid_cluster(cluster, bpb))
    {
        struct direntry *dirent = (struct direntry*)cluster_to_addr(cluster, image_buf, bpb);

        int numDirEntries=(bpb->bpbBytesPerSec*bpb->bpbSecPerClust)/sizeof(struct direntry);
        int i = 0;
	for ( ; i < numDirEntries; i++)
	{
            
            uint16_t followclust = metaFix(dirent, indent, image_buf, bpb, reff);
            if (followclust)//Cluster is not a file
            {
                follow_dir(followclust, indent+1, image_buf, bpb, reff);
            }
            dirent++;
	}

	cluster = get_fat_entry(cluster, image_buf, bpb);
    }
}

void traverse_root(uint8_t *image_buf, struct bpb33* bpb,uint16_t *reff)
{
    uint16_t cluster = 0;
    struct direntry *dirent = (struct direntry*)cluster_to_addr(cluster, image_buf, bpb);
    //Dirent now holds mem location of root cluster
    int i = 0;
    for ( ; i < bpb->bpbRootDirEnts; i++)
    {
        uint16_t followclust = metaFix(dirent, 0,image_buf,bpb,reff);
        if (is_valid_cluster(followclust, bpb))
        {
            follow_dir(followclust, 1, image_buf, bpb,reff);
        }
        dirent++;
    }
}

void orphanSearch(uint8_t *image_buf, struct bpb33* bpb,uint16_t *reff)
{
    printf("\n");
    uint16_t currCluster=CLUST_FIRST;
    uint16_t orphans[(bpb->bpbSectors/bpb->bpbSecPerClust)];
    uint16_t tmp[(bpb->bpbSectors/bpb->bpbSecPerClust)];//Used to make getClustSize work
    for(int j=0;j<(bpb->bpbSectors/bpb->bpbSecPerClust);j++)
    {
        tmp[j]=0;
        orphans[j]=0;
    }
    while(is_valid_cluster(currCluster,bpb))
    {
        if(get_fat_entry(currCluster,image_buf,bpb)!=CLUST_FREE)//cluster is not marked free
        {
            int found=0;
            for(int i=0;reff[i]!=0;i++)
            {
                if(currCluster==reff[i])
                {
                    found=1;
                    break;
                }
            }
            if(found==0)//We have an orphan!
            {
                int x=0;
                while(orphans[x]!=0)x++;
                orphans[x]=currCluster;
            }
        }
        currCluster++;
    }
    int num=0;
    //Now identify orphan heads
    for(int y=0;orphans[y]!=0;y++)
    {
        int found=0;
        currCluster=orphans[y];
        for(int l=0;orphans[l]!=0;l++)
        {
            if(currCluster==get_fat_entry(orphans[l],image_buf,bpb))
            {
                found=1;
                break;
            }
        }
        if(found==0)
        {
            num++;
            printf("Orphan head found at cluster: %u! Creating directory entry\n",orphans[y]);
            uint32_t fSize=getClustSize(orphans[y],image_buf,bpb,tmp,5);
            char fName[25];
            char fNum[5];
            sprintf(fNum,"%u",num);
            strcpy(fName,"found");
            strcat(fName,fNum);
            strcat(fName,".dat");
            struct direntry *root=(struct direntry*)cluster_to_addr(0,image_buf,bpb);
            create_dirent(root,fName,orphans[y],fSize,image_buf,bpb);
        }
    }
}

int main(int argc, char** argv) {
    uint8_t *image_buf;
    int fd;
    struct bpb33* bpb;
    if (argc < 2) {
	usage(argv[0]);
    }
    image_buf = mmap_file(argv[1], &fd);
    bpb = check_bootsector(image_buf);
    uint16_t numberOfClusts=(bpb->bpbSectors/bpb->bpbSecPerClust);
    uint16_t refClusts[numberOfClusts+1];//Referenced clusters
    for(int i=0;i<numberOfClusts+1;i++)refClusts[i]=0;//Filled with impossible values
    printf("\n");
    traverse_root(image_buf, bpb,refClusts);
    orphanSearch(image_buf,bpb,refClusts);
    unmmap_file(image_buf, &fd);
    return 0;
}
