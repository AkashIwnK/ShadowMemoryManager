/* String library that does not use system heap and depend on glibc string library */

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>
#include <stdint.h>
#include <math.h>
#include "Stringlib.h"

/* Implement memcpy for copying data */
void *__Safe_Memcpy(void *dest, const void *src, uint64_t numBytes)
{
/* Copy 8 bytes at a time */
	uint64_t *destPtr = (uint64_t *)dest;
	uint64_t *srcPtr = (uint64_t *)src;
	uint64_t size = numBytes >> 3;
	while(size--)
		*(destPtr++) = *(srcPtr++);

/* Deal with the rest of the bytes */
	size = numBytes % 8;
	if(size) {
		uint8_t *remDestPtr = (uint8_t *)destPtr;
		uint8_t *remSrcPtr = (uint8_t *)srcPtr;
		while(size--)
			*(remDestPtr++) = *(remSrcPtr++);
	}

	return (void *)dest;
}

/* Implement memset for setting numBytes to zero */
void *__Safe_Memset_Zero(void *memPtr, uint64_t numBytes)
{
/* Set 8 bytes at a time to zero */
	uint64_t *ptr = (uint64_t *)memPtr;
	uint64_t size = numBytes >> 3;
	while(size--)
		*(ptr++) = 0;

/* Deal with the rest of the bytes */
	size = numBytes % 8;
	if(size) {
		uint8_t *remPtr = (uint8_t *)ptr;
		while(size--)
			*(remPtr++) = 0;
	}

	return (void *)memPtr;
}

/* Here we assume that no string occupies the entire user address space */
uint64_t __Safe_Strlen(char *string)
{
	uint64_t numChar = 0;
	char *charPtr = string;
	while(*(charPtr++) != '\0')
		numChar++;
	return numChar;
}

/* Emulation of "strstr" function of the standard string library */
char *__Safe_Strstr(char *hayStack, char *needle)
{
/* Make sure that hayStack is at least as long as the needle */
	if(__Safe_Strlen(hayStack) < __Safe_Strlen(needle))
		return NULL;

/* Look for the needle in the hay stack */
	char *hayPtr = hayStack;
	while(*hayPtr) {
		char *needlePtr = needle;
		char *charPtr = hayPtr;
		while(*charPtr && *needlePtr && *charPtr == *needlePtr) {
			charPtr++;
			needlePtr++;
		}
		if(!*needlePtr)
			return --charPtr;
		hayPtr++;
	}
	return NULL;
}

void __Debug_Fprintf(int fd, char *message, ...)
{
	va_list arg;
	va_start(arg, message);
	__Safe_Fprintf(fd, message, arg);
	va_end(arg);
}

/* This printf is not supposed to use heap so this is a new version of 
 * simple printf for debugging purposes.
 */
void __Debug_Printf(char *message, ...)
{
	va_list arg;
	va_start(arg, message);
	__Safe_Fprintf(1, message, arg);
	va_end(arg);
}

void __Safe_Fprintf(int fd, char *message, va_list arglist)
{
/* A sanity check first */
	if(!message)
		return;

/* Printf buffer */
	char printf_buffer[4096] = {0};

/* We make the current printf buffer pointer */
	uint64_t cur_printfPtr = (uint64_t)printf_buffer;
	uint64_t temBufPtr = cur_printfPtr + 2048;

	va_list arg;
	va_copy (arg, arglist);
	char *string_start = message;
	char * string_end;
	while(1) {
		if((string_end = __Safe_Strstr(string_start, "%"))) {
			if(*(string_end + 1) == '%') {
			/* Look for the next character after '%' */
				string_start = string_end + 1;
				while(!(*string_start >= 97 && *string_start <= 122))
					string_start++;

				string_start++;
				continue;
			}

		/* Look for the next character after '%' */
			char * next_string_start = string_end + 1;
			while(!(*next_string_start >= 97 && *next_string_start <= 122))
				next_string_start++;
			next_string_start += 1;

		/* Allocate string in the buffer */
			char *cpy_char = string_start;
			char *buffer_stringSeg_ptr = (char *)cur_printfPtr;
			while(*cpy_char != '%')
				*((char *)cur_printfPtr++) = *(cpy_char++);

		/* Check what the user is planning to print. We have to do it ourselves because sprintf
		 * may not a reiable function in this case.
		 */
			string_end += 1;
			if(*string_end == 'c') {
				int int_form_char = va_arg(arg, int);
				if(!(int_form_char >= 0 && int_form_char < 128))
					va_end (arg);
				*((char *)cur_printfPtr++) = (char)int_form_char;
			} else {
				if(*string_end == 'd' || *string_end == 'i') {
				/* Get the integer and put it in the buffer one by one in the buffer */
					int64_t integer = va_arg(arg, int64_t);
					if(!integer) {
						*((char *)cur_printfPtr++) = '0';
					} else {
						if(integer < 0) {
						/* Now save '-' and then we take the absolute value of the integer */
							*((char *)cur_printfPtr++) = '-';
							integer = (~((int64_t)integer)) + 1;
						}

					/* First get the number of digits in the integer */
						uint64_t count = 1;
						int64_t digit = integer;
						uint64_t numDigits = 0;
						while(digit) {
							digit /= 10;
							count *= 10;
							numDigits++;
						}
						while(numDigits--) {
							count /= 10;
							digit = integer/count;
							*((char *)cur_printfPtr++) = digit + '0';
							integer -= (digit * count);
						}
					}
				} else {
					if(*string_end == 's') {
						cpy_char = va_arg(arg, char *);
						while(*cpy_char)
							*((char *)cur_printfPtr++) = *(cpy_char++);
					} else {
						if(*string_end == 'p') {
						/* Here we start storing the hexadecimal string in the reverse order of
						 * computation in the bottom of the buffer first.
						 */
							uint64_t quotient = va_arg(arg, uint64_t);
							if(!quotient) {
							/* Fill the buffer with "(nil)" */
								*((char *)cur_printfPtr++) = '(';
								*((char *)cur_printfPtr++) = 'n';
								*((char *)cur_printfPtr++) = 'i';
								*((char *)cur_printfPtr++) = 'l';
								*((char *)cur_printfPtr++) = ')';
								goto print_string;
							}
							uint64_t saved_quotient = quotient;
							uint64_t string_end;

						save_string:
						/* We keep track of the end of the string that is going to be stored in the buffer */
							*((char *)cur_printfPtr++) = '0';
							*((char *)cur_printfPtr++) = 'x';
							string_end = temBufPtr - 1;
							while (quotient) {
								uint64_t remainder;
								if(quotient < 16)
									remainder = quotient;
								else
									remainder = quotient % 16;
								if (remainder < 10)
									*((char *)(temBufPtr)++) = (char)(48 + remainder);
								else
									*((char *)(temBufPtr)++) = (char)(87 + remainder);
								quotient = quotient >> 4;
							}

						/* We are not done yet. We need to store the string to the rest of the
						 * string written near the top of the buffer.
						 */
							(temBufPtr)--;
							while(temBufPtr != string_end) {
								*((char *)cur_printfPtr++) = *((char *)(temBufPtr)--);
							}

						/* Restore the position of the mallocPtr pointer to the
						 * original position.
						 */
							(temBufPtr)++;

						/* If quotient is negative, we just make sure we convert it to a positive number */
							if(saved_quotient & ((uint64_t)1 << 63)) {
								quotient = (~saved_quotient) + 1;
								saved_quotient = quotient;

						/* We put the colon after the negative hexaddecimal number and a dash to indicate that
						 * it is a negative number.
						 */
								*((char *)cur_printfPtr++) = ':';
								*((char *)cur_printfPtr++) = ' ';
								*((char *)cur_printfPtr++) = '-';
								goto save_string;
							}
						} else {
						/*  Consider doubles */	
							if(*string_end == 'f') {
								double double_number = va_arg(arg, double);
								if(!double_number) {
									*((char *)cur_printfPtr++) = '0';
									*((char *)cur_printfPtr++) = '.';
									*((char *)cur_printfPtr++) = '0';
									*((char *)cur_printfPtr++) = '0';
								} else {
									double num;
									if(double_number > 0) {
										num = double_number;
									} else {
									/* Store the minus sign to denote negative number */
										*((char *)cur_printfPtr++) = '-';
										num = - double_number;
									}
									
									if(num >= 1) {
									/* We need to get the digits infront the decimal point */
										uint64_t integer = (uint64_t)num;
										
									/* First get the number of digits in the integer */
										uint64_t count = 1;
										uint64_t digit = integer;
										uint64_t numDigits = 0;
										while(digit) {
											digit /= 10;
											count *= 10;
											numDigits++;
										}
										
										uint64_t cast_integer = integer;
										while(numDigits--) {
											count /= 10;
											digit = integer/count;
											*((char *)cur_printfPtr++) = digit + '0';
											integer -= (digit * count);
										}
										
									/* Now, we just have the digits following the decimal point to deal with */
										num -= (double)cast_integer;
										//printf("num: %f\n", num);
										if(!num) {
										/* Store a decimal point and two zeroes */	
											*((char *)cur_printfPtr++) = '.';
											*((char *)cur_printfPtr++) = '0';
											*((char *)cur_printfPtr++) = '0';
											goto print_string;
										}
									} else {
										*((char *)cur_printfPtr++) = '0';
									}
									
								/* Now store the decimal point */	
									*((char *)cur_printfPtr++) = '.';
									
								/* Now we need to store the digits follwing the decimal point, so we get 
								 * all those digits.
								 */
									while(fmod(num, (double)10) >= 10e-5) {
										printf("zero:  %lf\n", (double)0.0);
										printf("-fmod: %lf\n", fmod(num, (double)10));
										printf("num: %lf\n", num);
										num *= 10;
									}
									
								/* Get rid of the last zero */
									uint64_t integer = (uint64_t)num;
									integer /= 10;
									
								/* Now store rest of the digits First get the number of digits 
								 * in the integer.
								 */
									uint64_t count = 1;
									uint64_t digit = integer;
									uint64_t numDigits = 0;
									while(digit) {
										digit /= 10;
										count *= 10;
										numDigits++;
									}
									while(numDigits--) {
										count /= 10;
										digit = integer/count;
										*((char *)cur_printfPtr++) = digit + '0';
										integer -= (digit * count);
									}
								}
							}
						}
					}
				}
			}

		print_string:
			*((char *)cur_printfPtr) = '\0';

			//cpy_char = buffer_stringSeg_ptr;
			uint64_t length = __Safe_Strlen(buffer_stringSeg_ptr);
			write(fd, (void *)buffer_stringSeg_ptr, length);
			//while(*cpy_char)
				//write(1, (void *)cpy_char++, 1);

			string_start = next_string_start;
		} else {
		/* Look for '\0' (end of the string) */
			string_end = string_start;
			while(*string_end)
				string_end++;

		/* Allocate string in the buffer */
			char *cpy_char = string_start;
			char *buffer_stringSeg_ptr = (char *)cur_printfPtr;
			while(cpy_char != string_end)
				*((char *)cur_printfPtr++) = *(cpy_char++);
			*((char *)cur_printfPtr) = '\0';

		/* Now, we use sprintf and print the string message in segments */
			//cpy_char = buffer_stringSeg_ptr;
			uint64_t length = __Safe_Strlen(buffer_stringSeg_ptr);
			write(fd, (void *)buffer_stringSeg_ptr, length);
			//while(*cpy_char)
			//	write(fd, (void *)cpy_char++, 1);
			break;
		}
	}
	va_end (arg);
}

/* We do not depend on the string library because apprently some functions can be unreliable */
void __Safe_Sprintf(char *string, uint64_t stringSize, char *insertString, ...)
{
/* Some sanity checks first */
	if(!string || !stringSize || !insertString)
		return;

/* Printf buffer */
	char sprintf_buffer[4096] = {0};

/* We make the current printf buffer pointer */
	uint64_t cur_printfPtr = (uint64_t)sprintf_buffer;
	uint64_t temBufPtr = cur_printfPtr + 2048;

	va_list arg;
	va_start (arg, insertString);
	char *string_start = insertString;
	char * string_end;
	uint64_t leftStringSize = stringSize;
	char *cur_string_ptr = string;
	while(1) {
		if((string_end = __Safe_Strstr(string_start, "%"))) {
			if(*(string_end + 1) == '%') {
			/* Look for the next character after '%' */
				string_start = string_end + 1;
				while(!(*string_start >= 97 && *string_start <= 122))
					string_start++;

				string_start++;
				continue;
			}

		/* Look for the next character after '%' */
			char * next_string_start = string_end + 1;
			while(!(*next_string_start >= 97 && *next_string_start <= 122))
				next_string_start++;
			next_string_start += 1;

		/* Allocate string in the buffer */
			char *cpy_char = string_start;
			char *buffer_stringSeg_ptr = (char *)cur_printfPtr;
			while(*cpy_char != '%')
				*((char *)cur_printfPtr++) = *(cpy_char++);

		/* Check what the user is planning to print. We have to do it ourselves because sprintf
		 * may not a reiable function in this case.
		 */
			string_end += 1;
			if(*string_end == 'c') {
				int int_form_char = va_arg(arg, int);
				if(!(int_form_char >= 0 && int_form_char < 128))
					va_end (arg);
				*((char *)cur_printfPtr++) = '0' + int_form_char;
			} else {
				if(*string_end == 'd' || *string_end == 'i') {
				/* Get the integer and put it in the buffer one by one in the buffer */
					int64_t integer = va_arg(arg, int64_t);
					if(!integer) {
						*((char *)cur_printfPtr++) = '0';
					} else {
						if(integer < 0) {
						/* Now save '-' and then we take the absolute value of the integer */
							*((char *)cur_printfPtr++) = '-';
							integer = (~((int64_t)integer)) + 1;
						}

					/* First get the number of digits in the integer */
						uint64_t count = 1;
						int64_t digit = integer;
						uint64_t numDigits = 0;
						while(digit) {
							digit /= 10;
							count *= 10;
							numDigits++;
						}
						while(numDigits--) {
							count /= 10;
							digit = integer/count;
							*((char *)cur_printfPtr++) = digit + '0';
							integer -= (digit * count);
						}
					}
				} else {
					if(*string_end == 's') {
						cpy_char = va_arg(arg, char *);
						while(*cpy_char)
							*((char *)cur_printfPtr++) = *(cpy_char++);
					} else {
						if(*string_end == 'p') {
						/* Here we start storing the hexadecimal string in the reverse order of
						 * computation in the bottom of the buffer first.
						 */
							uint64_t quotient = va_arg(arg, uint64_t);
							if(!quotient) {
							/* Fill the buffer with "(nil)" */
								*((char *)cur_printfPtr++) = '(';
								*((char *)cur_printfPtr++) = 'n';
								*((char *)cur_printfPtr++) = 'i';
								*((char *)cur_printfPtr++) = 'l';
								*((char *)cur_printfPtr++) = ')';
								goto sprint_string;
							}

						/* We keep track of the end of the string that is going to be stored in the buffer */
							*((char *)cur_printfPtr++) = '0';
							*((char *)cur_printfPtr++) = 'x';
							uint64_t string_end = temBufPtr - 1;
							while (quotient) {
								//printf("quotient: %"PRIu64"\n", quotient);
								uint64_t remainder;
								if(quotient < 16)
									remainder = quotient;
								else
									remainder = quotient % 16;
								if (remainder < 10)
									*((char *)(temBufPtr++)) = (char)(48 + remainder);
								else
									*((char *)(temBufPtr++)) = (char)(87 + remainder);
								quotient = quotient >> 4;
							}

						/* We are not done yet. We need to store the string to the rest of the
						 * string written near the top of the buffer.
						 */
							temBufPtr--;
							while(temBufPtr != string_end) {
								*((char *)cur_printfPtr++) = *((char *)(temBufPtr--));
							}

						/* Restore the position of the mallocPtr pointer to the
						 * original position.
						 */
							temBufPtr++;
						} else {
						/*  Consider doubles */	
							if(*string_end == 'f') {
								double double_number = va_arg(arg, double);
								if(!double_number) {
									*((char *)cur_printfPtr++) = '0';
									*((char *)cur_printfPtr++) = '.';
									*((char *)cur_printfPtr++) = '0';
									*((char *)cur_printfPtr++) = '0';
								} else {
									double num;
									if(double_number > 0) {
										num = double_number;
									} else {
									/* Store the minus sign to denote negative number */
										*((char *)cur_printfPtr++) = '-';
										num = - double_number;
									}
									
									if(num >= 1) {
									/* We need to get the digits infront the decimal point */
										uint64_t integer = (uint64_t)num;
										
									/* First get the number of digits in the integer */
										uint64_t count = 1;
										uint64_t digit = integer;
										uint64_t numDigits = 0;
										while(digit) {
											digit /= 10;
											count *= 10;
											numDigits++;
										}
										
										uint64_t cast_integer = integer;
										while(numDigits--) {
											count /= 10;
											digit = integer/count;
											*((char *)cur_printfPtr++) = digit + '0';
											integer -= (digit * count);
										}
										
									/* Now, we just have the digits following the decimal point to deal with */
										num -= (double)cast_integer;
										//printf("num: %f\n", num);
										if(!num) {
										/* Store a decimal point and two zeroes */	
											*((char *)cur_printfPtr++) = '.';
											*((char *)cur_printfPtr++) = '0';
											*((char *)cur_printfPtr++) = '0';
											goto sprint_string;
										}
									} else {
										*((char *)cur_printfPtr++) = '0';
									}
									
								/* Now store the decimal point */	
									*((char *)cur_printfPtr++) = '.';
									
								/* Now we need to store the digits follwing the decimal point, so we get 
								 * all those digits.
								 */
									while(fmod(num, (double)10) >= 10e-5) {
										printf("zero:  %lf\n", (double)0.0);
										printf("-fmod: %lf\n", fmod(num, (double)10));
										printf("num: %lf\n", num);
										num *= 10;
									}
									
								/* Get rid of the last zero */
									uint64_t integer = (uint64_t)num;
									integer /= 10;
									
								/* Now store rest of the digits First get the number of digits 
								 * in the integer.
								 */
									uint64_t count = 1;
									uint64_t digit = integer;
									uint64_t numDigits = 0;
									while(digit) {
										digit /= 10;
										count *= 10;
										numDigits++;
									}
									while(numDigits--) {
										count /= 10;
										digit = integer/count;
										*((char *)cur_printfPtr++) = digit + '0';
										integer -= (digit * count);
									}
								}
							}
						}
					}
				}
			}

		sprint_string:
			*((char *)cur_printfPtr) = '\0';

			cpy_char = buffer_stringSeg_ptr;
			while(*cpy_char && leftStringSize) {
				*(cur_string_ptr++) = *(cpy_char++);
				leftStringSize--;
			}
			if(!leftStringSize)
				break;

			string_start = next_string_start;
		} else {
		/* Look for '\0' (end of the string) */
			string_end = string_start;
			while(*string_end)
				string_end++;

		/* Allocate string in the buffer */
			char *cpy_char = string_start;
			char *buffer_stringSeg_ptr = (char *)cur_printfPtr;
			while(cpy_char != string_end)
				*((char *)cur_printfPtr++) = *(cpy_char++);
			*((char *)cur_printfPtr) = '\0';

		/* Now, we use sprintf and print the string message in segments */
			cpy_char = buffer_stringSeg_ptr;
			while(*cpy_char && leftStringSize) {
				*(cur_string_ptr++) = *(cpy_char++);
				leftStringSize--;
			}
			break;
		}
	}
	va_end (arg);
}

/* Works slightly different from the standard strtoull function.
 * Returns -1 on error and sets the second argument to NULL.
 */
uint64_t __Safe_Strtoull_Base16(char *hexString, char **firstInvalidStringAddr)
{
/* Perform some sanity checks first */
	if(!hexString) {
		*firstInvalidStringAddr = NULL;
		return -1;
	}

/* The beginning spaces can be ignored though */
	char *stringStart = hexString;
	while(*stringStart == ' ')
		stringStart++;

/* DO NOT skip spaces and look for "0x" in the beginning of the string.
 * Spaces may mark the end of the given hexadecimal string.
 */
	if(*stringStart == '0' && *(stringStart + 1) == 'x')
		stringStart += 2;

/* Now, we mark the beginning of the string and find the "valid" end of the string.
 * Meaning that any non-numberic or letter following 'f'/'F' is considered invalid.
 * We also have to check if the format of the string is consistent with
 */
	char *stringEnd = stringStart;
	int lowerCaseFormat = 0;
	int upperCaseFormat = 0;

traverseHexString:
	while(*stringEnd >= '0' && *stringEnd <= '9') {
		stringEnd++;
		goto traverseHexString;
	}
	while (*stringEnd >= 'a' && *stringEnd <= 'f') {
	/* If upper case format was used and lower case format use is detected,
	 * we can either return an error or just stop here and deal with the
	 * traversed string. It is probably better to be conservative so we'll
	 * just throw an error.
	 */
		if(upperCaseFormat) {
			*firstInvalidStringAddr = NULL;
			return -1;
		}
		lowerCaseFormat = 1;
		stringEnd++;
		goto traverseHexString;
	}
	while (*stringEnd >= 'A' && *stringEnd <= 'F') {
	/* If lower case format was used and upper case format use is detected,
	 * we can either return an error or just stop here and deal with the
	 * traversed string. It is probably better to be conservative so we'll
	 * just throw an error.
	 */
		if(lowerCaseFormat) {
			*firstInvalidStringAddr = NULL;
			return -1;
		}
		upperCaseFormat = 1;
		stringEnd++;
		goto traverseHexString;
	}

/* If the string is invalid right from the beginning, return -1 and set the second
 * argumment of the function to NULL.
 */
	if(stringEnd == stringStart) {
		*firstInvalidStringAddr = NULL;
		return -1;
	}

/* Set the value for the invalid char pointer to pointer */
	*firstInvalidStringAddr = stringEnd;
	stringEnd--; /* Decrement to make it point to the last valid character of hexString */

/* Now,that we have checked if the format of the string is correct, we proceed to compute the
 * numerical value of the hex in the string from the end, all the way up to the beginning of it.
 */
	uint64_t value = 0;
	uint64_t numBytes = 0;
	while(stringEnd >= stringStart) {
		uint64_t fourByteVal = 0;
		if(*stringEnd >= '0' && *stringEnd <= '9') {
			fourByteVal = (uint64_t)(*stringEnd - '0');
		} else {
			if(*stringEnd >= 'a' && *stringEnd <= 'f') {
				fourByteVal = 10 + (uint64_t)(*stringEnd - 'a');
			} else {
				fourByteVal = 10 + (uint64_t)(*stringEnd - 'A');
			}
		}
		value += fourByteVal*((uint64_t)1 << numBytes); /* Scale for the number of bytes traversed */
		stringEnd--;
		numBytes += 4; /* Here we are looking at 4 bytes at a time */
	}
	return value;
}

int64_t __Safe_Atoi(char *string)
{
/* First a sanity check */
	if(!string)
		return (int64_t)SAFE_ATOI_ERROR;

/* We iterate through the string and see if the number is potentially a negative number */
	int8_t numIsNeg = 0;
	char *charPtr = string;
	while(*charPtr == ' ')
		charPtr++;
	if(__Safe_Strstr(string, "-")) {
	/* This means that the number is probably negative. Skip all the spaces.
	 * Check if the number starts with a minus sign. If not, return error.
	 */
		if(*charPtr != '-')
			return (int64_t)SAFE_ATOI_ERROR;

	/* Now that we have established that the number is negative, we get the number */
		numIsNeg = 1;
		charPtr++;
	}

/* Now we scan through the rest of the string to make sure that it conatains valid numbers.
 * At the same time we count the number of digits.
 */
	char *ptr = charPtr;
	uint64_t count = 0;
	while(*ptr) {
		if(!(*ptr >= 48 && *ptr <= 57)) {
		/* If we hit a character that is not a number, we check if it is a space.
		 * Now, the string si expected to end with space all the rest of the way through.
		 */
			while(*ptr) {
				if(*ptr != ' ') {
				/* If the character is not a space, we return an error */
					return (int64_t)SAFE_ATOI_ERROR;
				}
				ptr++;
			}
			break;
		}
		ptr++;
		count++;
	}

/* Return error if the string is empty */
	if(!count)
		return (int64_t)SAFE_ATOI_ERROR;

/* Now we compute the multiplier */
	uint64_t multiplier = 1;
	count -= 1;
	while(count--)
		multiplier *= 10;

/* Now we iterate through the string again to compute the number */
	int64_t	number = 0;
	int64_t digit;
	while(*charPtr) {
		digit = (int64_t)*charPtr - 48;
		number += digit*multiplier;
		multiplier /= 10;
		charPtr++;
	}

/* If the number is meant to be a negative number, return it */
	if(numIsNeg)
		return ((~number) + 1);

	return number;
}

