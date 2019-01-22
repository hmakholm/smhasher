// Spooky Hash
// A 128-bit noncryptographic hash, for checksums and table lookup
// By Bob Jenkins.  Public domain.
//   Oct 31 2010: published framework, disclaimer ShortHash isn't right
//   Nov 7 2010: disabled ShortHash
//   Oct 31 2011: replace End, ShortMix, ShortEnd, enable ShortHash again
//   April 10 2012: buffer overflow on platforms without unaligned reads
//   July 12 2012: was passing out variables in final to in/out in short
//   July 30 2012: I reintroduced the buffer overflow
//   August 5 2012: SpookyV2: d = should be d += in short hash, and remove extra mix from long hash

#include <memory.h>
#include "Spookier.h"

#define ALLOW_UNALIGNED_READS 1

INLINE void SpookierHash::ShortInner(
    const uint64 *message,
    size_t length,
    bool abfree,
    uint64 a, uint64 b, uint64 c, uint64 d,
    uint64 *out1, uint64 *out2)
{
    union 
    { 
        const uint8 *p8; 
        const uint32 *p32;
        const uint64 *p64; 
        size_t i; 
    } u;

    u.p64 = message;

    size_t remainder = length;

    if (remainder > 15)
    {
        if( abfree ) {
            a += u.p64[0];
            b += u.p64[1];
            u.p64 += 2;
            remainder -= 16;
        }
      
        // handle all complete sets of 32 bytes
        const uint64 *end = u.p64 + (remainder/32)*4;
        for (; u.p64 < end; u.p64 += 4)
        {
            c += u.p64[0];
            d += u.p64[1];
            ShortMix(a,b,c,d);
            a += u.p64[2];
            b += u.p64[3];
        }
        remainder %= 32;
        
        //Handle the case of 16+ remaining bytes.
        if (remainder >= 16)
        {
            c += u.p64[0];
            d += u.p64[1];
            ShortMix(a,b,c,d);
            u.p64 += 2;
            remainder -= 16;
        }
    }
    
    // Handle the last 0..15 bytes, and its length
    d += ((uint64)length) << 56;
    switch (remainder)
    {
    case 15:
        d += ((uint64)u.p8[14]) << 48;
    case 14:
        d += ((uint64)u.p8[13]) << 40;
    case 13:
        d += ((uint64)u.p8[12]) << 32;
    case 12:
        d += u.p32[2];
        c += u.p64[0];
        break;
    case 11:
        d += ((uint64)u.p8[10]) << 16;
    case 10:
        d += ((uint64)u.p8[9]) << 8;
    case 9:
        d += (uint64)u.p8[8];
    case 8:
        c += u.p64[0];
        break;
    case 7:
        c += ((uint64)u.p8[6]) << 48;
    case 6:
        c += ((uint64)u.p8[5]) << 40;
    case 5:
        c += ((uint64)u.p8[4]) << 32;
    case 4:
        c += u.p32[0];
        break;
    case 3:
        c += ((uint64)u.p8[2]) << 16;
    case 2:
        c += ((uint64)u.p8[1]) << 8;
    case 1:
        c += (uint64)u.p8[0];
        break;
    case 0:
        c += sc_const;
        d += sc_const;
    }
    ShortEnd(a,b,c,d);
    *out1 = a;
    *out2 = b;
}

void SpookierHash::Short(
    const void *message,
    size_t length,
    uint64 *hash1,
    uint64 *hash2)
{
    uint64 buf[2*sc_numVars];
    if (!ALLOW_UNALIGNED_READS && ((size_t)message & 0x7) != 0)
    {
        memcpy(buf, message, length);
        message = (const void*)buf;
    }
    ShortInner((const uint64*)message, length, false,
               *hash1, *hash2, sc_const, sc_const,
               hash1, hash2);
}

INLINE void SpookierHash::End(
    const uint64 *data, size_t length,
    uint64 h0, uint64 h1, uint64 h2, uint64 h3,
    uint64 h4, uint64 h5, uint64 h6, uint64 h7, 
    uint64 h8, uint64 h9, uint64 h10,uint64 h11,
    uint64 *out1, uint64 *out2)
{
  // Hash the 12-word state down to 4 words for the final partial block
  // .., backwards, because the last words are in the most need of
  // diffusion at this point.
  ShortMix(h11, h10, h9, h8);
  h8 += h4; h9 += h5; h10 += h6; h11 += h7;
  ShortMix(h11, h10, h9, h8);
  h8 += h0; h9 += h1; h10 += h2; h11 += h3;
  // omit the last ShortMix since the data in h0 through h3 has already
  // been diffused pretty well by Mix() before the finish, so it should be
  // harmless to add message data directly together with them.
  // ShortMix(h11, h10, h9, h8);
  
  // Handle the final block with the short hash
  ShortInner(data, length, true, h11, h10, h9, h8, out1, out2);
}

// do the whole hash in one call
void SpookierHash::Hash128(
    const void *message, 
    size_t length, 
    uint64 *hash1, 
    uint64 *hash2)
{
    if (length < sc_bufSize)
    {
        Short(message, length, hash1, hash2);
        return;
    }

    uint64 h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11;
    uint64 buf[sc_numVars];
    uint64 *end;
    union 
    { 
        const uint8 *p8; 
        uint64 *p64; 
        size_t i; 
    } u;
    size_t remainder;
    
    h0=h3=h6=h9  = *hash1;
    h1=h4=h7=h10 = *hash2;
    h2=h5=h8=h11 = sc_const;
    
    u.p8 = (const uint8 *)message;
    end = u.p64 + (length/sc_blockSize)*sc_numVars;

    // handle all whole sc_blockSize blocks of bytes
    if (ALLOW_UNALIGNED_READS || ((u.i & 0x7) == 0))
    {
        while (u.p64 < end)
        { 
            Mix(u.p64, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
	    u.p64 += sc_numVars;
        }
    }
    else
    {
        while (u.p64 < end)
        {
            memcpy(buf, u.p64, sc_blockSize);
            Mix(buf, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
	    u.p64 += sc_numVars;
        }
    }

    // handle the last partial block of sc_blockSize bytes
    remainder = (length - ((const uint8 *)end-(const uint8 *)message));
    if (!ALLOW_UNALIGNED_READS && ((u.i & 0x7) != 0))
    {
        memcpy(buf, end, remainder);
        end = buf;
    }
    End(end, remainder, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11, hash1, hash2);
}



// init spooky state
void SpookierHash::Init(uint64 seed1, uint64 seed2)
{
    m_length = 0;
    m_remainder = 0;
    m_state[0] = seed1;
    m_state[1] = seed2;
}


// add a message fragment to the state
void SpookierHash::Update(const void *message, size_t length)
{
    uint64 h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11;
    size_t newLength = length + m_remainder;
    uint8  remainder;
    union 
    { 
        const uint8 *p8; 
        uint64 *p64; 
        size_t i; 
    } u;
    const uint64 *end;
    
    // Is this message fragment too short?  If it is, stuff it away.
    if (newLength < sc_bufSize)
    {
        memcpy(&((uint8 *)m_data)[m_remainder], message, length);
        m_length = length + m_length;
        m_remainder = (uint8)newLength;
        return;
    }
    
    // init the variables
    if (m_length < sc_bufSize)
    {
        h0=h3=h6=h9  = m_state[0];
        h1=h4=h7=h10 = m_state[1];
        h2=h5=h8=h11 = sc_const;
    }
    else
    {
        h0 = m_state[0];
        h1 = m_state[1];
        h2 = m_state[2];
        h3 = m_state[3];
        h4 = m_state[4];
        h5 = m_state[5];
        h6 = m_state[6];
        h7 = m_state[7];
        h8 = m_state[8];
        h9 = m_state[9];
        h10 = m_state[10];
        h11 = m_state[11];
    }
    m_length = length + m_length;
    
    // if we've got anything stuffed away, use it now
    if (m_remainder)
    {
        uint8 prefix = sc_bufSize-m_remainder;
        memcpy(&(((uint8 *)m_data)[m_remainder]), message, prefix);
        u.p64 = m_data;
        Mix(u.p64, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
        Mix(&u.p64[sc_numVars], h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
        u.p8 = ((const uint8 *)message) + prefix;
        length -= prefix;
    }
    else
    {
        u.p8 = (const uint8 *)message;
    }
    
    // handle all whole blocks of sc_blockSize bytes
    end = u.p64 + (length/sc_blockSize)*sc_numVars;
    remainder = (uint8)(length-((const uint8 *)end-u.p8));
    if (ALLOW_UNALIGNED_READS || (u.i & 0x7) == 0)
    {
        while (u.p64 < end)
        { 
            Mix(u.p64, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
	    u.p64 += sc_numVars;
        }
    }
    else
    {
        while (u.p64 < end)
        { 
            memcpy(m_data, u.p8, sc_blockSize);
            Mix(m_data, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
	    u.p64 += sc_numVars;
        }
    }

    // stuff away the last few bytes
    m_remainder = remainder;
    memcpy(m_data, end, remainder);
    
    // stuff away the variables
    m_state[0] = h0;
    m_state[1] = h1;
    m_state[2] = h2;
    m_state[3] = h3;
    m_state[4] = h4;
    m_state[5] = h5;
    m_state[6] = h6;
    m_state[7] = h7;
    m_state[8] = h8;
    m_state[9] = h9;
    m_state[10] = h10;
    m_state[11] = h11;
}


// report the hash for the concatenation of all message fragments so far
void SpookierHash::Final(uint64 *hash1, uint64 *hash2)
{
    // init the variables
    if (m_length < sc_bufSize)
    {
        ShortInner(m_data, m_length, false,
                   m_state[0], m_state[1], sc_const, sc_const,
                   hash1, hash2);
        return;
    }
    
    const uint64 *data = (const uint64 *)m_data;
    uint8 remainder = m_remainder;
    
    uint64 h0 = m_state[0];
    uint64 h1 = m_state[1];
    uint64 h2 = m_state[2];
    uint64 h3 = m_state[3];
    uint64 h4 = m_state[4];
    uint64 h5 = m_state[5];
    uint64 h6 = m_state[6];
    uint64 h7 = m_state[7];
    uint64 h8 = m_state[8];
    uint64 h9 = m_state[9];
    uint64 h10 = m_state[10];
    uint64 h11 = m_state[11];

    if (remainder >= sc_blockSize)
    {
        // m_data can contain two blocks; handle any whole first block
        Mix(data, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11);
        data += sc_numVars;
        remainder -= sc_blockSize;
    }
    End(data, remainder, h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11, hash1, hash2);
}
