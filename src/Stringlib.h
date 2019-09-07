/* String library header */

#ifndef __STRINGLIB_H_
#define __STRINGLIB_H_


#define SAFE_ATOI_ERROR ((int64_t)1 << 63)

/************* STRING FUNCTIONS ************/

void *__Safe_Memcpy(void *dest, const void *src, uint64_t numBytes);
void *__Safe_Memset_Zero(void *memPtr, uint64_t numBytes);
uint64_t __Safe_Strlen(char *string);
char *__Safe_Strstr(char *hayStack, char *needle);
void __Debug_Printf(char *message, ...);
void __Debug_Fprintf(int fd, char *message, ...);
void __Safe_Fprintf(int fd, char *message, va_list arglist);
void __Safe_Sprintf(char *string, uint64_t stringSize, char *insertString, ...);
uint64_t __Safe_Strtoull_Base16(char *hexString, char **firstInvalidStringAddr);
int64_t __Safe_Atoi(char *string);

#endif  /* __STRINGLIB_H_ */
