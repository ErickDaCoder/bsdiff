/*-
 * Copyright 2003-2005 Colin Percival
 * Copyright 2012 Matthew Endsley
 * Copyright 2024 Erick Ortiz
 * All rights reserved
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted providing that the following conditions 
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 */

#include "bsdiff.h"

#include <limits.h>
#include <string.h>
#include <sys/stat.h>

#define MIN(x,y) (((x)<(y)) ? (x) : (y))

static void split(int64_t* indices, int64_t* values, int64_t start, int64_t length, int64_t offset) {
    int64_t i, j, k, pivotValue, tmp, rangeStart, rangeEnd;
    if (length < 16) {
        for (k = start; k < start + length; k += j) {
            j = 1;
            pivotValue = values[indices[k] + offset];
            for (i = 1; k + i < start + length; i++) {
                if (values[indices[k + i] + offset] < pivotValue) {
                    pivotValue = values[indices[k + i] + offset];
                    j = 0;
                }
                if (values[indices[k + i] + offset] == pivotValue) {
                    tmp = indices[k + j];
                    indices[k + j] = indices[k + i];
                    indices[k + i] = tmp;
                    j++;
                }
            }
            for (i = 0; i < j; i++) values[indices[k + i]] = k + j - 1;
            if (j == 1) indices[k] = -1;
        }
        return;
    }
    pivotValue = values[indices[start + length / 2] + offset];
    rangeStart = 0;
    rangeEnd = 0;
    for (i = start; i < start + length; i++) {
        if (values[indices[i] + offset] < pivotValue) rangeStart++;
        if (values[indices[i] + offset] == pivotValue) rangeEnd++;
    }
    rangeStart += start;
    rangeEnd += rangeStart;
    i = start;
    j = 0;
    k = 0;
    while (i < rangeStart) {
        if (values[indices[i] + offset] < pivotValue) {
            i++;
        } else if (values[indices[i] + offset] == pivotValue) {
            tmp = indices[i];
            indices[i] = indices[rangeStart + j];
            indices[rangeStart + j] = tmp;
            j++;
        } else {
            tmp = indices[i];
            indices[i] = indices[rangeEnd + k];
            indices[rangeEnd + k] = tmp;
            k++;
        }
    }
    while (rangeStart + j < rangeEnd) {
        if (values[indices[rangeStart + j] + offset] == pivotValue) {
            j++;
        } else {
            tmp = indices[rangeStart + j];
            indices[rangeStart + j] = indices[rangeEnd + k];
            indices[rangeEnd + k] = tmp;
            k++;
        }
    }
    if (rangeStart > start) split(indices, values, start, rangeStart - start, offset);

    for (i = 0; i < rangeEnd - rangeStart; i++) values[indices[rangeStart + i]] = rangeEnd - 1;
    if (rangeStart == rangeEnd - 1) indices[rangeStart] = -1;

    if (start + length > rangeEnd) split(indices, values, rangeEnd, start + length - rangeEnd, offset);
}

static void quickSuffixSort(int64_t* suffixArray, int64_t* sortedGroup, const uint8_t* inputString, int64_t inputSize) {
    int64_t charFreq[256];
    int64_t i, height, groupLen;
    memset(charFreq, 0, 256);
    for (i = 0; i < inputSize; i++)
        charFreq[inputString[i]]++;
    for (i = 1; i < 256; i++)
        charFreq[i] += charFreq[i - 1];
    for (i = 255; i > 0; i--)
        charFreq[i] = charFreq[i - 1];
    charFreq[0] = 0;
    for (i = 0; i < inputSize; i++)
        suffixArray[++charFreq[inputString[i]]] = i;
    suffixArray[0] = inputSize;
    for (i = 0; i < inputSize; i++)
        sortedGroup[i] = charFreq[inputString[i]];
    sortedGroup[inputSize] = 0;
    for (i = 1; i < 256; i++)
        if (charFreq[i] == charFreq[i - 1] + 1)
            suffixArray[charFreq[i]] = -1;
    suffixArray[0] = -1;
    for (height = 1; suffixArray[0] != -(inputSize + 1); height += height) {
        groupLen = 0;
        for (i = 0; i < inputSize + 1;) {
            if (suffixArray[i] < 0) {
                groupLen -= suffixArray[i];
                i -= suffixArray[i];
            } else {
                if (groupLen) suffixArray[i - groupLen] = -groupLen;
                groupLen = sortedGroup[suffixArray[i]] + 1 - i;
                split(suffixArray, sortedGroup, i, groupLen, height);
                i += groupLen;
                groupLen = 0;
            }
        }
        if (groupLen)
            suffixArray[i - groupLen] = -groupLen;
    }
    for (i = 0; i < inputSize + 1; i++)
        suffixArray[sortedGroup[i]] = i;
}

static int64_t calcMatchingLength(const uint8_t* oldData, int64_t oldDataSize, const uint8_t* newData,
                                  int64_t newDataSize) {
    int64_t matchLength;
    for (matchLength = 0; matchLength < oldDataSize && matchLength < newDataSize; matchLength++)
        if (oldData[matchLength] != newData[matchLength])
            break;
    return matchLength;
}

static int64_t binSearchSuffixArray(const int64_t* suffixArray, const uint8_t* oldData, int64_t oldDataSize,
                                    const uint8_t* newData, int64_t newDataSize, int64_t start, int64_t end,
                                    int64_t* bestMatchPosition) {
    int64_t x;
    if (end - start < 2) {
        int64_t y;
        x = calcMatchingLength(oldData + suffixArray[start], oldDataSize - suffixArray[start], newData, newDataSize);
        y = calcMatchingLength(oldData + suffixArray[end], oldDataSize - suffixArray[end], newData, newDataSize);
        if (x > y) {
            *bestMatchPosition = suffixArray[start];
            return x;
        }
        *bestMatchPosition = suffixArray[end];
        return y;
    }
    x = start + (end - start) / 2;
    if (memcmp(oldData + suffixArray[x], newData,MIN(oldDataSize-suffixArray[x], newDataSize)) < 0)
        return binSearchSuffixArray(suffixArray, oldData, oldDataSize, newData, newDataSize, x, end, bestMatchPosition);
    return binSearchSuffixArray(suffixArray, oldData, oldDataSize, newData, newDataSize, start, x, bestMatchPosition);
}

static void offsetToBytes(const int64_t offset, uint8_t* bytebuf) {
    int64_t _offset;

    if (offset < 0)
        _offset = -offset;
    else
        _offset = offset;

    bytebuf[0] = _offset % 256;
    _offset -= bytebuf[0];
    _offset = _offset / 256;
    bytebuf[1] = _offset % 256;
    _offset -= bytebuf[1];
    _offset = _offset / 256;
    bytebuf[2] = _offset % 256;
    _offset -= bytebuf[2];
    _offset = _offset / 256;
    bytebuf[3] = _offset % 256;
    _offset -= bytebuf[3];
    _offset = _offset / 256;
    bytebuf[4] = _offset % 256;
    _offset -= bytebuf[4];
    _offset = _offset / 256;
    bytebuf[5] = _offset % 256;
    _offset -= bytebuf[5];
    _offset = _offset / 256;
    bytebuf[6] = _offset % 256;
    _offset -= bytebuf[6];
    _offset = _offset / 256;
    bytebuf[7] = _offset % 256;

    if (offset < 0)
        bytebuf[7] |= 0x80;
}

static int64_t writedata(struct bsdiff_stream* stream, const void* buffer, int64_t length) {
    int64_t result = 0;
    while (length > 0) {
        const int smallsize = MIN(length, INT_MAX);
        const int writeresult = stream->write(stream, buffer, smallsize);
        if (writeresult == -1)
            return -1;
        result += writeresult;
        length -= smallsize;
        buffer = (uint8_t*) buffer + smallsize;
    }
    return result;
}

struct bsdiff_request {
    const uint8_t* old;
    int64_t oldsize;
    const uint8_t* new;
    int64_t newsize;
    struct bsdiff_stream* stream;
    int64_t* I;
    uint8_t* buffer;
};

static int bsdiff_internal(const struct bsdiff_request req) {
    int64_t* suffix_array,* rank_array;
    int64_t currentScan, matchedPosition, matchedLength;
    int64_t lastScan, lastMatchedPosition, lastOffset;
    int64_t oldscore, scoreCompare;
    int64_t score, scoreFront, lengthFront, scoreBack, lengthBack;
    int64_t overlapLength, scoreOverlap, lengthOverlap;
    int64_t i;
    uint8_t* diffBuf;
    uint8_t controlBuf[8 * 3];
    if ((rank_array = req.stream->malloc((req.oldsize + 1) * sizeof(int64_t))) == NULL) return -1;
    suffix_array = req.I;
    quickSuffixSort(suffix_array, rank_array, req.old, req.oldsize);
    req.stream->free(rank_array);
    diffBuf = req.buffer;
    /* Compute the differences, writing ctrl as we go */
    currentScan = 0;
    matchedLength = 0;
    matchedPosition = 0;
    lastScan = 0;
    lastMatchedPosition = 0;
    lastOffset = 0;
    while (currentScan < req.newsize) {
        oldscore = 0;
        for (scoreCompare = currentScan += matchedLength; currentScan < req.newsize; currentScan++) {
            matchedLength = binSearchSuffixArray(suffix_array, req.old, req.oldsize, req.new + currentScan,
                                                 req.newsize - currentScan,
                                                 0, req.oldsize, &matchedPosition);
            for (; scoreCompare < currentScan + matchedLength; scoreCompare++)
                if ((scoreCompare + lastOffset < req.oldsize) &&
                    (req.old[scoreCompare + lastOffset] == req.new[scoreCompare]))
                    oldscore++;
            if (((matchedLength == oldscore) && (matchedLength != 0)) ||
                (matchedLength > oldscore + 8))
                break;
            if ((currentScan + lastOffset < req.oldsize) &&
                (req.old[currentScan + lastOffset] == req.new[currentScan]))
                oldscore--;
        }
        if (matchedLength != oldscore || currentScan == req.newsize) {
            score = 0;
            scoreFront = 0;
            lengthFront = 0;
            for (i = 0; (lastScan + i < currentScan) && (lastMatchedPosition + i < req.oldsize);) {
                if (req.old[lastMatchedPosition + i] == req.new[lastScan + i]) score++;
                i++;
                if (score * 2 - i > scoreFront * 2 - lengthFront) {
                    scoreFront = score;
                    lengthFront = i;
                };
            };

            lengthBack = 0;
            if (currentScan < req.newsize) {
                score = 0;
                scoreBack = 0;
                for (i = 1; (currentScan >= lastScan + i) && (matchedPosition >= i); i++) {
                    if (req.old[matchedPosition - i] == req.new[currentScan - i]) score++;
                    if (score * 2 - i > scoreBack * 2 - lengthBack) {
                        scoreBack = score;
                        lengthBack = i;
                    };
                };
            };

            if (lastScan + lengthFront > currentScan - lengthBack) {
                overlapLength = (lastScan + lengthFront) - (currentScan - lengthBack);
                score = 0;
                scoreOverlap = 0;
                lengthOverlap = 0;
                for (i = 0; i < overlapLength; i++) {
                    if (req.new[lastScan + lengthFront - overlapLength + i] ==
                        req.old[lastMatchedPosition + lengthFront - overlapLength + i])
                        score++;
                    if (req.new[currentScan - lengthBack + i] ==
                        req.old[matchedPosition - lengthBack + i])
                        score--;
                    if (score > scoreOverlap) {
                        scoreOverlap = score;
                        lengthOverlap = i + 1;
                    };
                };

                lengthFront += lengthOverlap - overlapLength;
                lengthBack -= lengthOverlap;
            };

            offsetToBytes(lengthFront, controlBuf);
            offsetToBytes((currentScan - lengthBack) - (lastScan + lengthFront), controlBuf + 8);
            offsetToBytes((matchedPosition - lengthBack) - (lastMatchedPosition + lengthFront), controlBuf + 16);

            /* Write control data */
            if (writedata(req.stream, controlBuf, sizeof(controlBuf)))
                return -1;

            /* Write diff data */
            for (i = 0; i < lengthFront; i++)
                diffBuf[i] = req.new[lastScan + i] - req.old[lastMatchedPosition + i];
            if (writedata(req.stream, diffBuf, lengthFront))
                return -1;

            /* Write extra data */
            for (i = 0; i < (currentScan - lengthBack) - (lastScan + lengthFront); i++)
                diffBuf[i] = req.new[lastScan + lengthFront + i];
            if (writedata(req.stream, diffBuf, (currentScan - lengthBack) - (lastScan + lengthFront)))
                return -1;

            lastScan = currentScan - lengthBack;
            lastMatchedPosition = matchedPosition - lengthBack;
            lastOffset = matchedPosition - currentScan;
        };
    };

    return 0;
}

int bsdiff(const uint8_t* old, int64_t oldsize, const uint8_t* new, int64_t newsize, struct bsdiff_stream* stream) {
    int result;
    struct bsdiff_request req;

    if ((req.I = stream->malloc((oldsize + 1) * sizeof(int64_t))) == NULL)
        return -1;

    if ((req.buffer = stream->malloc(newsize + 1)) == NULL) {
        stream->free(req.I);
        return -1;
    }

    req.old = old;
    req.oldsize = oldsize;
    req.new = new;
    req.newsize = newsize;
    req.stream = stream;

    result = bsdiff_internal(req);

    stream->free(req.buffer);
    stream->free(req.I);

    return result;
}

#if defined(BSDIFF_EXECUTABLE)

#include <sys/types.h>

#include <bzlib.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <io.h>
#include <share.h>

static int bz2_write(struct bsdiff_stream* stream, const void* buffer, int size) {
    int bz2err;
    BZFILE* bz2;

    bz2 = stream->opaque;
    BZ2_bzWrite(&bz2err, bz2, (void*) buffer, size);
    if (bz2err != BZ_STREAM_END && bz2err != BZ_OK)
        return -1;

    return 0;
}

int onfile(
    const char* const name,
    off_t* restrict const size,
    uint8_t** restrict const buffer) {
    /* Allocate *size + 1 bytes instead of *size bytes to ensure
        that we never try to malloc(0) and get a NULL pointer */
    int fd;
    if (_sopen_s(&fd, name, _O_RDONLY | _O_BINARY, _SH_DENYRW, _S_IREAD) != 0) {
        printf("Failed to open file \"%s\" (errno %d)", name, errno);
        return 1;
    }
    if ((*size = _lseek(fd, 0, SEEK_END)) == -1) {
        printf("Failed to seek to end of file \"%s\" (errno %d)", name, errno);
        return 1;
    }
    if ((*buffer = malloc(*size + 1)) == NULL) {
        printf("Failed to allocate memory reading file \"%s\" (errno %d)", name, errno);
        return 1;
    }
    if (_lseek(fd, 0, SEEK_SET) != 0) {
        printf("Failed to seek in file \"%s\" (errno %d)", name, errno);
        return 1;
    }
    int readresult = _read(fd, *buffer, *size);
    if (readresult != *size) {
        printf("Failed to read contents of file \"%s\" (read %d, not %ld) (errno %d)", name, readresult, *size, errno);
        return 1;
    }
    if (_close(fd) == -1) {
        printf("Failed to close file \"%s\" (errno %d)", name, errno);
        return 1;
    }
    return 0;
}

int main(int argc, char* argv[]) {
    int bz2err;
    uint8_t* old,* new;
    off_t oldsize, newsize;
    uint8_t buf[8];
    FILE* pf;
    struct bsdiff_stream stream;
    BZFILE* bz2;

    memset(&bz2, 0, sizeof(bz2));
    stream.malloc = malloc;
    stream.free = free;
    stream.write = bz2_write;

    if (argc != 4) {
        printf("usage: %s oldfile newfile patchfile\n", argv[0]);
        return 1;
    }

    if (onfile(argv[1], &oldsize, &old) != 0)
        return 1;

    if (onfile(argv[2], &newsize, &new) != 0)
        return 1;

    /* Create the patch file */
    if (fopen_s(&pf, argv[3], "wb") != 0) {
        printf("%s (errno %d)", argv[3], errno);
        return 1;
    }

    /* Write header (signature+newsize)*/
    offsetToBytes(newsize, buf);
    if (fwrite("ENDSLEY/BSDIFF43", 16, 1, pf) != 1 ||
        fwrite(buf, sizeof(buf), 1, pf) != 1) {
        printf("Failed to write header");
        return 1;
    }


    if (NULL == (bz2 = BZ2_bzWriteOpen(&bz2err, pf, 9, 0, 0))) {
        printf("BZ2_bzWriteOpen, bz2err=%d", bz2err);
        return 1;
    }

    stream.opaque = bz2;
    if (bsdiff(old, oldsize, new, newsize, &stream)) {
        printf("bsdiff");
        return 1;
    }

    BZ2_bzWriteClose(&bz2err, bz2, 0, NULL, NULL);
    if (bz2err != BZ_OK) {
        printf("BZ2_bzWriteClose, bz2err=%d", bz2err);
        return 1;
    }

    if (fclose(pf)) {
        printf("fclose");
        return 1;
    }

    /* Free the memory we used */
    free(old);
    free(new);

    return 0;
}

#endif
