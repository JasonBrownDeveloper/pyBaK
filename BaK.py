import functools
import itertools
import math
import pprint
import statistics
import struct
import sys
import time
import tkinter
import tkinter.font
import tkinter.ttk

import PIL.Image
import PIL.ImageTk
import PIL.ImageOps
import PIL.ImageChops

import matplotlib.pyplot as plt
import matplotlib.patches as pch
import numpy as np

def Dynamix_LZW(length, compressed):
    dict_table = []
    code_size = 0
    cache_bits = 0
    dict_full = False
    code_cur = []
    dict_max = 0

    def Dynamix_LZW_reset():
        nonlocal dict_table
        nonlocal code_size
        nonlocal cache_bits
        nonlocal dict_full
        nonlocal code_cur
        nonlocal dict_max
        dict_table = [bytes([x]) for x in range(256)]
        dict_table.append(None) # 0x100 is reset code
        code_size = 9
        cache_bits = 0
        dict_full = False
        code_cur = []
        dict_max = 0x200

    bitarray = ''.join(["{:08b}".format(x) for x in compressed[::-1]])
    buf_out = []

    Dynamix_LZW_reset()

    while len(buf_out) < length:
        code = int(bitarray[-code_size:], 2)
        bitarray = bitarray[:-code_size]
        if code == 0xFFFFFFFF:
            return buf_out

        cache_bits = cache_bits + code_size
        if cache_bits >= code_size * 8:
            cache_bits = cache_bits - (code_size * 8)

        if code == 0x100:
            if cache_bits > 0:
                bitarray = bitarray[:-((code_size * 8) - cache_bits)]

            Dynamix_LZW_reset()
            continue

        if code >= len(dict_table) and dict_full == False:
            code_cur.append(code_cur[0])
            buf_out += code_cur
        else:
            buf_out += dict_table[code]
            code_cur.append(dict_table[code][0])

        if len(code_cur) >= 2:
            if dict_full == False:
                if len(dict_table) == dict_max and code_size == 12:
                    dict_full = True
                else:
                    cache_bits = 0

                if len(dict_table)+1 == dict_max and code_size < 12:
                    dict_max = dict_max * 2
                    code_size = code_size + 1

                dict_table.append(code_cur)

            code_cur = list(dict_table[code])

    return buf_out

# Oddly this is the same compression scheme used by Chrono Trigger
def Dynamix_LZSS(length, compressed):
    buf_out = []

    while len(buf_out) < length:
        header = compressed.pop(0)
        for b in "{:08b}".format(header)[::-1]:
            if b == "1":
                buf_out.append(compressed.pop(0))
            else:
                offset, = struct.unpack("<H", compressed[:2])
                run_length = compressed[2] + 5
                del compressed[:3]
                buf_out += buf_out[offset:offset+run_length]

            if len(buf_out) >= length:
                break

    return buf_out

def Dynamix_RLE(length, compressed):
    buf_out = []

    while len(buf_out) < length:
        header = compressed.pop(0)
        if header & 0x80:
            buf_out += [ compressed.pop(0) ] * (header & 0x7f)
        else:
            buf_out += compressed[:header]
            del compressed[:header]

    return buf_out

#TODO change index to BufferedReader
def LoadTags(raw):
    index = 0
    tags = {}
    while index < len(raw):
        label, size = struct.unpack("<4sI", raw[index:index+8])
        index = index + 8
        if size & 0x80000000:
            size = size & ~0x80000000
            tags[label[:-1].decode()] = LoadTags(raw[index:index+size])
        else:
            tags[label[:-1].decode()] = raw[index:index+size]
        index = index + size
    return tags

def LoadTagFNT(FNT):
    index = 0
    format = "<HBBBBHBI"
    format_size = struct.calcsize(format)
    _, height, _, first, count, _, compression, size = struct.unpack(format, FNT[index:index+format_size])
    index = index + format_size
    if compression != 1:
        print("Unsupported compression", compression)
        return None

    raw = bytes(Dynamix_RLE(size, bytearray(FNT[index:])))

    glyphs = []
    for i in range(count):
        offset, = struct.unpack("<H", raw[i*2:i*2+2])
        width, = struct.unpack("<B", raw[count*2+i:count*2+i+1])
        if width <= 8:
            format = ">B"
            format_size = 1
        else:
            format = ">H"
            format_size = 2

        glyph = []
        for j in range(height):
            line, = struct.unpack(format, raw[count*3+offset+j*format_size:count*3+offset+j*format_size+format_size])
            if width <= 8: line = line << 8
            glyph.append(line)

        glyphs.append(glyph)

    return glyphs

def LoadTagINF(INF):
    index = 0
    count, = struct.unpack("<H", INF[index:index+2])
    index = index + 2 + 1
    offsets = []
    for _ in range(count):
        offsets.append( struct.unpack("<HI", INF[index:index+6]) )
        index = index + 6

    return offsets

def LoadTagPAG(PAG):
    index = 0
    return struct.unpack("<H", PAG[index:index+2])[0]

def LoadTagPAL(PAL):
    palette = {}
    for k, v in PAL.items():
        palette[k] = eval("LoadTag"+k+"(v)")
    return palette

def LoadTagRES(RES):
    index = 0
    count, = struct.unpack("<H", RES[index:index+2])
    index = index + 2
    ress = []
    for _ in range(count):
        id, = struct.unpack("<H", RES[index:index+2])
        index = index + 2
        nul = RES.index(b'\x00', index)
        res, = struct.unpack("<"+str(nul-index)+"s", RES[index:nul])
        index = nul + 1
        ress.append( (id, res) )
    return ress

def LoadTagSCR(SCR):
    index = 0
    compression, = struct.unpack("<B", SCR[index:index+1])
    index = index + 1
    if compression != 2:
        print("Unsupported compression", key, compression)
        return None

    screen_size, = struct.unpack("<I", SCR[index:index+4])
    index = index + 4
    screen = Dynamix_LZW(screen_size, SCR[index:])
    return screen

def LoadTagTAG(TAG):
    index = 0
    count, = struct.unpack("<H", TAG[index:index+2])
    index = index + 2
    tags = []
    for _ in range(count):
        id, = struct.unpack("<H", TAG[index:index+2])
        index = index + 2
        nul = TAG.index(b'\x00', index)
        name, = struct.unpack("<"+str(nul-index)+"s", TAG[index:nul])
        index = nul + 1
        tags.append( (id, name) )
    return tags

def LoadTagTT3(TT3):
    index = 1
    tt3_size, = struct.unpack("<I", TT3[index:index+4])
    index = index + 4
    raw = bytes(Dynamix_RLE(tt3_size, bytearray(TT3[index:])))
    raw_index = 0
    chunks = []
    while raw_index < len(raw):
        code, = struct.unpack("<H", raw[raw_index:raw_index+2])
        raw_index = raw_index + 2

        csize = code & 0x000f
        ccode = code & 0xfff0
        chunks.append( {"code":ccode, "data":[]} )
        if ccode == 0x1110 and csize == 1:
            id, = struct.unpack("<H", raw[raw_index:raw_index+2])
            raw_index = raw_index + 2
            chunks[-1]["data"].append(id) 
        elif csize == 15:
            nul = raw.index(b'\x00', raw_index)
            name, = struct.unpack("<"+str(nul-raw_index)+"s", raw[raw_index:nul])
            raw_index = nul + 1
            chunks[-1]["name"] = name.decode().upper()
            raw_index = raw_index + 1 if raw_index & 0x1 else raw_index
        else:
            for _ in range(csize):
                chunks[-1]["data"].append( *struct.unpack("<h", raw[raw_index:raw_index+2]) )
                raw_index = raw_index + 2

    return chunks

def LoadTagTTI(TTI):
    return None

def LoadTagVER(VER):
    index = 0
    size = len(VER)
    version, = struct.unpack("<"+str(size)+"s", VER[index:index+size])
    index = index + size
    version = version.rstrip(b'\x00').decode()
    return version

def LoadTagVGA(VGA):
    palette = []
    index = 0
    for c in range(index, index+len(VGA), 3):
        r, g, b = struct.unpack("<BBB", VGA[c:c+3])
        palette.extend( [r<<2, g<<2, b<<2] )
    return palette

def LoadADS(ADS):
    animation = {}
    for k, v in LoadTags(ADS).items():
        animation[k] = eval("LoadTag"+k+"(v)")
    return animation

def LoadBMX(BMX):
    index = 0
    format = "<HHHHI"
    format_size = struct.calcsize(format)
    magic, compression, image_count, data_size, raw_size = struct.unpack(format, BMX[index:index+format_size])
    index = index + format_size
    if magic != 0x1066:
        # TODO BOOK.BMX 0x4D42
        # Possibly low color hi res
        print("Unsupported magic number", hex(magic))
        return None

    format = "<HHHH"
    format_size = struct.calcsize(format)
    images = []
    for _ in range(image_count):
        images.append( dict(zip(["data_size", "flags", "width", "height"]
            , struct.unpack(format, BMX[index:index+format_size]))) )
        index = index + format_size

    # LZW
    if compression == 0:
        format = "<BI"
        format_size = struct.calcsize(format)
        magic, lzw_size = struct.unpack(format, BMX[index:index+format_size])
        index = index + format_size
        assert(magic == 0x02)
        assert(raw_size == lzw_size)
        raw = Dynamix_LZW(raw_size, bytearray(BMX[index:]))
    elif compression == 1:
        raw = Dynamix_LZSS(raw_size, bytearray(BMX[index:]))
    elif compression == 2:
        raw = Dynamix_RLE(raw_size, bytearray(BMX[index:]))
    else:
        print("Unsupported compression", compression)
        return None

    raw_index = 0
    for image in images:
        if image["flags"] & 0x20:
            image["width"], image["height"] = image["height"], image["width"]
        if image["flags"] & 0x80:
            pixels = Dynamix_RLE(image["width"] * image["height"], bytearray(raw[raw_index:]))
        else:
            pixels = raw[raw_index:raw_index+image["data_size"]]

        image["image"] = PIL.Image.frombytes("PA", (image["width"], image["height"])
            , bytes([a for p in pixels for a in (p, p if not p else 0xff)]).ljust(image["width"] * image["height"], b'\x00'))

        if image["flags"] & 0x60 == 0x60:
            image["image"] = image["image"].rotate(270, expand=True)
            image["width"], image["height"] = image["height"], image["width"]
            image["image"] = PIL.ImageOps.mirror(image["image"])
        elif image["flags"] & 0x20 == 0x20:
            image["image"] = image["image"].rotate(270, expand=True)
            image["width"], image["height"] = image["height"], image["width"]
        elif image["flags"] & 0x40:
            # Don't want to mirror if its not also rotated, don't know why
            pass

        raw_index = raw_index + image["data_size"]
    return images

def LoadBOK(BOK):
    file_size, = struct.unpack("<I", BOK[:4])
    page_count, = struct.unpack("<H", BOK[4:6])
    page_offsets = list(struct.unpack("<"+str(page_count)+"I", BOK[6:6+4*page_count]))
    pages = []
    for offset in page_offsets:
        index = 4 + offset
        format = "<hhhhHHHHHHHHH"
        format_size = struct.calcsize(format)
        ( ypos, xpos, width, height, number, id, prevId, _
            , nextId, flag, numDecorations, numFirstLetters
            , showNumber ) = struct.unpack(format, BOK[index:index+format_size])
        index = index + format_size + 30
        decorations = []
        for _ in range(numDecorations):
            dypos, dxpos, did, dflag = struct.unpack("<hhHH", BOK[index:index+8])
            decorations.append( (dypos, dxpos, did, dflag) )
            index = index + 8
        firstLetters = []
        for _ in range(numFirstLetters):
            fypos, fxpos, fid, fflag = struct.unpack("<hhHH", BOK[index:index+8])
            firstLetters.append( (fypos, fxpos, fid, fflag) )
            index = index + 8
        EOP = BOK.index(b'\xF0', index)
        text = BOK[index:index+EOP]
        pages.append( (ypos, xpos, width, height, number, id, prevId
            , nextId, flag, numDecorations, numFirstLetters
            , showNumber, decorations, firstLetters, text) )
    return pages

def LoadDDX(DDX):
    found = []
    def LoadBranch(DDX, offset):
        index = 5 + offset
        child_count, unk_count, length = struct.unpack("<BBH", DDX[index:index+4])
        index = index + 4
        children = []
        for _ in range(child_count):
            index = index + 4
            type, child_offset = struct.unpack("<hI", DDX[index:index+6])
            index = index + 6
            children.append( (type, child_offset) )

        for _ in range(child_count):
            type, child_offset = children.pop(0)
            if not child_offset & 0x80000000 and child_offset not in found:
                found.append(child_offset)
                children.append(LoadBranch(DDX, child_offset))

        index = index + unk_count * 10
        try:
            nul = DDX.index(b'\x00', index)
        except:
            if index == len(DDX):
                nul = index
            else:
                raise
        text, = struct.unpack("<"+str(nul-index)+"s", DDX[index:index+(nul-index)])
        return (text, children)

    count, = struct.unpack("<H", DDX[:2])
    index = 2
    offsets = []
    for _ in range(count):
        id, offset = struct.unpack("<II", DDX[index:index+8])
        offsets.append( (id, offset) )
        index = index + 8

    dialog = []
    for id, offset in offsets:
        dialog.append( (id, LoadBranch(DDX, offset)) )

    return dialog

def LoadFNT(FNT):
    glyphs = {}
    for k, v in LoadTags(FNT).items():
        glyphs[k] = eval("LoadTag"+k+"(v)")
    return glyphs

def LoadGAM(GAM):
    index = 106
    format = "<IIIBBBII"
    format_size = struct.calcsize(format)
    yloc, xloc, _, zone, xcell, ycell, ypos, xpos = struct.unpack(format, GAM[index:index+format_size])
    index = index + format_size + 5
    heading = struct.unpack("<H", GAM[index:index+2])
    index = index + 2 + 23

    party = []
    for _ in range(6):
        name = struct.unpack("<10s", GAM[index:index+10])[0].rstrip(b'\x00')
        index = index + 10
        party.append( {"name":name} )

    for i in range(6):
        stats = []
        index = index + 8
        for _ in range(16):
            stats.append(struct.unpack("<5B", GAM[index:index+5]))
            index = index + 5
        index = index + 7
        party[i]["stats"] = stats

    count, = struct.unpack("<B", GAM[index:index+1])
    index = index + 1
    active = struct.unpack("<"+str(count)+"B", GAM[index:index+count])

    index = 0x03a7f8
    for i in range(6):
        unk_count, = struct.unpack("<H", GAM[index:index+2])
        index = index + 2 + unk_count

        items = []
        item_count, slot_count = struct.unpack("<BH", GAM[index:index+3])
        index = index + 3
        for _ in range(slot_count):
            items.append( struct.unpack("<BBH", GAM[index:index+4]) )
            index = index + 4
        index = index + 1
        party[i]["items"] = items

    return (yloc, xloc, zone, xcell, ycell, ypos, xpos, heading, party, active)

def LoadLBL(LBL):
    count, = struct.unpack("<H", LBL[:2])

    index = 2
    labels = []
    for _ in range(count):
        format = "<hhhhbb"
        format_size = struct.calcsize(format)
        labels.append(list(struct.unpack(format, LBL[index:index+format_size])))
        index = index + format_size
    start = index + 2
    for i in range(count):
        if labels[i][0] >= 0:
            index = start + labels[i][0]
            nul = LBL.index(b'\x00', index)
            labels[i].append(struct.unpack("<"+str(nul-index)+"s", LBL[index:index+(nul-index)])[0])

    return labels

def LoadPAL(PAL):
    palette = {}
    for k, v in LoadTags(PAL).items():
        palette[k] = eval("LoadTag"+k+"(v)")
    return palette

def LoadREQ(REQ):
    index = 2
    format = "<h2Bhhhh2Bhh"
    format_size = struct.calcsize(format)
    box = struct.unpack(format, REQ[index:index+format_size])
    index = index + format_size + 8

    count, = struct.unpack("<H", REQ[index:index+2])
    index = index + 2

    data = []
    for _ in range(count):
        format = "<HhB6BhhHH2BhhH2BH"
        format_size = struct.calcsize(format)
        data.append( list(struct.unpack(format, REQ[index:index+format_size])) )
        index = index + format_size + 2

    start = index + 2
    for i in range(count):
        if data[i][15] >= 0:
            index = start + data[i][15]
            nul = REQ.index(b'\x00', index)
            data[i].append( struct.unpack("<"+str(nul-index)+"s", REQ[index:index+(nul-index)])[0] )
    return data

def LoadSCX(SCX):
    width = 320
    height = 200

    index = 3 # Skip Magic Number 0x27b6
    raw_size, = struct.unpack("<I", SCX[index:index+4])
    index = index + 4

    raw = Dynamix_LZW(raw_size, SCX[index:])

    return PIL.Image.frombytes("PA", (width, height), bytes([a for p in raw for a in (p, p if not p else 0xff)]).ljust(width * height, b'\x00'))

def LoadSX(SX):
    sound = {}
    for k, v in LoadTags(SX).items():
        if k == "DAT":
            index = 0
            format = "<HBHIH"
            format_size = struct.calcsize(format)
            id, type, _, raw_size, _ = struct.unpack(format, SX[index:index+format_size])
            index = index + format_size
            start = index

            type, = struct.unpack("<B", SX[index:index+1])
            index = index + 1
            data = []

            sounds = []
            while type != 0xFF:
                code, = struct.unpack("<B", SX[index:index+1])
                index = index + 1
                samp_offsets = []
                while code != 0xFF:
                    index = index + 1
                    samp_offsets.append( struct.unpack("<HH", SX[index:index+4]) )
                    index = index + 4
                    code, = struct.unpack("<B", SX[index:index+1])
                    index = index + 1

                voices = []
                for samp_offset, samp_size in samp_offsets:
                    samp_offset = start + samp_offset
                    voices.append( SX[samp_offset:samp_offset+samp_size] )
                sounds.append( voices )
                type, = struct.unpack("<B", SX[index:index+1])
                index = index + 1
            data.append( (id, type, sounds) )
            sound[k] = data
        else:
            sound[k] = eval("LoadTag"+k+"(v)")
    return sound

def LoadTBL(TBL):
    items = []
    for k, v in LoadTags(TBL).items():
        if k == "MAP":
            index = 2
            count, = struct.unpack("<H", v[index:index+2])
            index = index + 2
            offsets = []
            for _ in range(count):
                offsets.append( struct.unpack("<H", v[index:index+2])[0] )
                index = index + 2 
            index = index + 2
            start = index
            for offset in offsets:
                index = start + offset
                nul = v.index(b'\x00', index)
                items.append( {"MAP":struct.unpack("<"+str(nul-index)+"s", v[index:nul])[0].decode()} )
        elif k == "APP":
            pass
        elif k == "GID":
            index = 0
            offsets = []
            for _ in range(len(items)):
                low, high = struct.unpack("<HH", v[index:index+4])
                index = index + 4
                offsets.append( (high << 4) + (low & 0xF) )
            for i, offset in enumerate(offsets):
                index = offset
                items[i]["GID"] = dict(zip(["xradius", "yradius", "type", "count", "unknown", "unknown2"], struct.unpack("<HHBBBB", v[index:index+8])))
                index = index + 8
                length = sorted([n for n in offsets + [len(v)] if n > offset])[0]
                items[i]["GID"]["raw"] = list(map("{:02X}".format,v[offset:length]))
                if items[i]["GID"]["type"] == 0:
                    items[i]["GID"]["textures"] = []
                    for _ in range(items[i]["GID"]["count"]):
                        header = {"unknown":struct.unpack("<2B", v[index:index+2])}
                        index = index + 2
                        header["count"] = struct.unpack("<H", v[index:index+2])[0]
                        index = index + 2
                        header["unknown2"] = struct.unpack("<2B", v[index:index+2])
                        index = index + 2
                        items[i]["GID"]["textures"].append( {"header":header} )
                    for t in items[i]["GID"]["textures"]:
                        t["coords"] = []
                        for _ in range(t["header"]["count"]):
                            t["coords"].append(list(zip(["u", "v", "x", "y"], struct.unpack("<bbhh", v[index:index+6]))))
                            index = index + 6
                else:
                    items[i]["GID"]["textures"] = ["TODO"]

        elif k == "DAT":
            index = 0

            offsets = []
            while True:
                low, high = struct.unpack_from("<HH", v, index)
                index += 4
                offset = (high << 4) + (low & 0xF)
                if not offset:
                    break
                offsets.append( offset )

            for i, offset in enumerate(offsets):
                #length = sorted([n for n in offsets + [len(v)] if n > offset])[0]
                #items[i]["DAT"]["raw"] = list(map("{:02X}".format,v[offset:length]))
                #print( items[i]["MAP"] )

                items[i]["DAT"] = dict(zip(
                      ["flags", "type", "terrain", "scale"]
                    , struct.unpack_from("<BBBB", v, offset + 0)))

                items[i]["DAT"] |= dict(zip(
                      ["animation count", "animation offset"]
                    , struct.unpack_from("<HH", v, offset + 4)))

                # All offsets are themselves offset from the base offset
                items[i]["DAT"] |= dict(zip(
                      ["model count", "base offset", "u1", "u2"]
                    , struct.unpack_from("<HH2B", v, offset + 8)))

                if not items[i]["DAT"]["flags"] & 0x20: # UNBOUNDED
                    minx, miny, minz, maxx, maxy, maxz = struct.unpack_from(
                          "<hhhhhh"
                        , v
                        , offset + 14 )
                    items[i]["DAT"] |= {
                          "min":(minx, miny, minz)
                        , "max":(maxx, maxy, maxz) }

                for j in range( items[i]["DAT"]["model count"] ):
                    items[i]["DAT"].setdefault("model", []).append( dict(zip(
                          ["u1", "u2", "mesh count", "mesh offset"]
                        , struct.unpack_from(
                              "<2BHH"
                            , v
                            , offset + 14
                                + ( 12 if not items[i]["DAT"]["flags"] & 0x20 else 0 )
                                + ( j * 6 ) ))) )

                # all offsets are from the start of the model table
                offset += 14 + ( 12 if not items[i]["DAT"]["flags"] & 0x20 else 0 )

                for j in range( items[i]["DAT"]["animation count"] ):
                    items[i]["DAT"].setdefault("animation", []).append( dict(zip(
                          ["u1", "u2", "u3", "u4", "u5", "u6", "u7", ]
                        , struct.unpack_from(
                              "<7B"
                            , v
                            , offset
                                + items[i]["DAT"]["animation offset"]
                                - items[i]["DAT"]["base offset"]
                                + ( j * 7 ) ))) )

                if 'model' not in items[i]["DAT"]:
                    continue

                for model in items[i]["DAT"]["model"]:
                    for j in range( model[ "mesh count" ] ):
                        model.setdefault("mesh", []).append( dict(zip(
                              [ "u1"
                                , "u2"
                                , "u3"
                                , "vertex count"
                                , "vertex offset"
                                , "face count"
                                , "face offset"
                                , "u4"
                                , "u5"
                                , "u6"
                                , "u7" ]
                            , struct.unpack_from(
                                  "<3BBHHH4B"
                                , v
                                , offset
                                    + model[ "mesh offset" ]
                                    - items[i]["DAT"]["base offset"]
                                    + ( j * 14 ) ))) )

                def chain_siblings( siblings, parent ):
                    return functools.reduce(
                          lambda l, k: itertools.chain( *[ v.get(k, []) for v in l ] )
                        , siblings
                        , parent )

                vertex_set = {
                    ( mesh["vertex count"], mesh["vertex offset"] )
                    for mesh in chain_siblings( [ "mesh" ], items[i]["DAT"]["model"] ) }

                vertex = {}
                for vcount, voffset in vertex_set:
                    vertex[ voffset ] = []
                    for j in range( vcount ):
                        vertex[ voffset ].append( struct.unpack_from(
                              "<hhh"
                            , v
                            , offset
                                + voffset
                                - items[i]["DAT"]["base offset"]
                                + ( j * 6 ) ) )

                for mesh in chain_siblings( [ "mesh" ], items[i]["DAT"]["model"] ):
                    if items[i]["DAT"]["terrain"] and not items[i]["DAT"]["scale"]: # FIELD
                        mesh["pos"] = vertex[ mesh[ "vertex offset" ] ][0]

                    for j in range( mesh[ "face count" ] ):
                        mesh.setdefault("face", []).append( dict(zip(
                              [ "type"
                                , "edge count"
                                , "edge offset"
                                , "u1"
                                , "u2" ]
                            , struct.unpack_from(
                                  "<HHH2B"
                                , v
                                , offset
                                    + mesh[ "face offset" ]
                                    - items[i]["DAT"]["base offset"]
                                    + ( j * 8 ) ))) )

                for face in chain_siblings( [ "mesh", "face" ], items[i]["DAT"]["model"] ):
                    if face[ "type" ] == 0:
                        for j in range( face[ "edge count" ] ):
                            face.setdefault("edge", []).append( dict(zip(
                                  [ "u1"
                                    , "color1"
                                    , "color2"
                                    , "color3"
                                    , "color4"
                                    , "group"
                                    , "vertex offset" ]
                                , struct.unpack_from(
                                      "<B4BBH"
                                    , v
                                    , offset
                                        + face[ "edge offset" ]
                                        - items[i]["DAT"]["base offset"]
                                        + ( j * 8 ) ))) )

                        for edge in chain_siblings( [ "mesh", "face", "edge" ], items[i]["DAT"]["model"] ):
                            nul = v.index( b'\xFF', offset + edge["vertex offset"] - items[i]["DAT"]["base offset"] )
                            edge[ "vertex" ] = struct.unpack_from(
                                  "<"+str( nul - ( offset + edge["vertex offset"] - items[i]["DAT"]["base offset"] ) )+"B"
                                , v
                                , offset
                                    + edge["vertex offset"]
                                    - items[i]["DAT"]["base offset"]
                                    )

                        # convert vertex indexes to vertices
                        for mesh in chain_siblings( [ "mesh" ], items[i]["DAT"]["model"] ):
                            for edge in chain_siblings( [ "edge" ], mesh[ "face" ] ):
                                edge[ "vertex" ] = [
                                    vertex[ mesh[ "vertex offset" ] ][p]
                                    for p in edge[ "vertex" ] ]

                    elif face[ "type" ] == 2:
                        items[i]["DAT"]["sprite"] = face[ "edge count" ]

    return items

def LoadTTM(TTM):
    movie = {}
    for k, v in LoadTags(TTM).items():
        movie[k] = eval("LoadTag"+k+"(v)")
    return movie

def LoadWLD(WLD):
    index = 0
    world = []
    while index < len(WLD):
        world.append( dict(zip(["type", "xrot", "yrot", "zrot", "xloc", "yloc", "zloc"]
            , struct.unpack("<HHHHIII", WLD[index:index+20]))) )
        index = index + 20

    return world

class Movie(object):
    def __init__(self, tk, surface, scale, ttm, canvas):
        self.tk = tk
        self.surface = surface
        self.scale = scale
        self.ttm = LoadTTM(resources[ttm])
        self.canvas = canvas
        self.rect = None

        self.backbuffer = PIL.Image.new("PA", (320, 200))
        self.frontbuffer = PIL.Image.new("PA", (320, 200))
        self.frontpalette = None
        self.saved = None
        self.sprites = {}
        self.sprite = None
        self.palettes = {}
        self.palette = None
        self.screen = None
        self.snippet = None
        self.delay = 0
        self.index = 0
        self.render_queue = []
        self.fadeby = None

    def Render(self):
        if self.saved: self.backbuffer.paste(self.saved)
        if self.snippet: self.backbuffer.paste(self.snippet, (self.snippetX, self.snippetY))
        for r, x, y in self.render_queue:
            if r:
                self.backbuffer.paste(r, (x, y), r.getchannel("A"))

    def Flip(self):
        self.frontbuffer.paste(self.backbuffer)
        if self.palette in self.palettes: self.frontpalette = self.palettes[self.palette].copy()

    def Refresh(self):
        if self.frontpalette: self.frontbuffer.putpalette(self.frontpalette)
        self.surface.paste(self.frontbuffer.convert("RGB").resize((320*self.scale, 200*self.scale)))

    def Next(self):
        while self.index < len(self.ttm["TT3"]):
            chunk = self.ttm["TT3"][self.index]
            if chunk["code"] == 0x0020: # SAVE_BACKGROUND
                print("save bg")
                self.Render()
                if not self.saved: self.saved = PIL.Image.new("PA", (320, 200))
                self.saved.paste(self.backbuffer)
                pass
            elif chunk["code"] == 0x0080: # DRAW_BACKGROUND
                print("draw bg")
                pass
            elif chunk["code"] == 0x0110: # PURGE
                print("pruge")
                self.saved = None
                self.snippet = None
                pass
            elif chunk["code"] == 0x0ff0: # UPDATE
                print("update")
                self.Render()
                self.Flip()
                self.Refresh()
                self.render_queue.clear()
                if self.delay:
                    print("***done")
                    tk.after(self.delay, self.Next)
                    self.index = self.index + 1
                    break
                #self.index = self.index + 1
                #break
                pass
            elif chunk["code"] == 0x1020: # DELAY
                print("set delay")
                self.delay = chunk["data"][0] * 10
                pass
            elif chunk["code"] == 0x1050: # SLOT_IMAGE
                print("pick sprite", hex(chunk["data"][0]))
                self.sprite = chunk["data"][0]
                pass
            elif chunk["code"] == 0x1060: # SLOT_PALETTE
                print("pick palette")
                self.palette = chunk["data"][0]
                pass
            elif chunk["code"] == 0x1110: # SET_SCENE
                print("scene", list(map(hex, chunk["data"])), chunk.get("name", None))
                pass
            elif chunk["code"] in (0x2000, 0x2010): # SET_FRAME01
                print("frame", list(map(hex, chunk["data"])), chunk.get("name", None))
                pass
            elif chunk["code"] == 0x4000: # CROP
                print("crop")
                # may not need to crop if it's always masked anyway
                x, y, w, h = chunk["data"]
                self.canvas.create_rectangle( (x*self.scale, y*self.scale, w*self.scale, h*self.scale), outline="Red")
            elif chunk["code"] == 0x4110: # FADE_OUT
                first, number, steps, delay = chunk["data"]

                if self.frontpalette is None:
                    print("fade out")
                    print("no palette")
                    print("***done")
                    self.index = self.index + 1
                    tk.after(delay, self.Next)
                    break

                if self.fadeby is None:
                    print("fade out")
                    self.fadeto = [0] * number*3
                    self.fade = self.frontpalette[first*3:(first+number)*3]
                    percent = 1 / (64 << (steps & 0xf))
                    self.fadeby = [c * percent for c in self.fade]

                self.fade = [c - p for c, p in zip(self.fade, self.fadeby)]
                self.frontpalette[first*3:(first+number)*3] = [max(t, int(c)) for c, t in zip(self.fade, self.fadeto)]
                self.Refresh()

                if all(v == t for v, t in zip(self.fade, self.fadeto)):
                    print("***done")
                    self.fadeto = None
                    self.fadeby = None
                    self.fade = None
                    self.index = self.index + 1
                #else:
                tk.after(delay, self.Next)
                break
                pass
            elif chunk["code"] == 0x4120: # FADE_IN
                first, number, steps, delay = chunk["data"]

                if self.frontpalette is None:
                    print("fade in")
                    print("no palette")
                    print("***done")
                    self.index = self.index + 1
                    tk.after(delay, self.Next)
                    break

                if self.fadeby is None:
                    print("fade in")
                    self.Render()
                    self.Flip()
                    self.fadeto = self.frontpalette[first*3:(first+number)*3]
                    self.fade = [0] * number*3
                    percent = 1 / (64 << (steps & 0xf))
                    self.fadeby = [c * percent for c in self.fadeto]

                self.fade = [c + p for c, p in zip(self.fade, self.fadeby)]
                self.frontpalette[first*3:(first+number)*3] = [min(t, int(c)) for c, t in zip(self.fade, self.fadeto)]
                self.Refresh()

                if all(v == t for v, t in zip(self.fade, self.fadeto)):
                    print("***done")
                    self.fadeto = None
                    self.fadeby = None
                    self.fade = None
                    self.index = self.index + 1
                #else:
                tk.after(delay, self.Next)
                break
                pass
            elif chunk["code"] in (0x4200, 0x4210): # SAVE_IMAGE01
                print("snippet")
                self.snippetX, self.snippetY, w, h = chunk["data"]
                self.snippet = self.backbuffer.crop( (self.snippetX, self.snippetY, w, h) )
                pass
            elif chunk["code"] == 0xa100: # ERASE
                print("erase")
                if self.saved: self.saved.paste(0x00, (chunk["data"][0], chunk["data"][1], chunk["data"][0]+chunk["data"][2], chunk["data"][1]+chunk["data"][3]))
                pass
            elif chunk["code"] in (0xa500, 0xa510, 0xa520, 0xa530, 0xa5a0): # DRAW_SPRITE0123
                if chunk["data"][3] in self.sprites and chunk["data"][2] < len(self.sprites[chunk["data"][3]]):
                    print("draw sprite", hex(chunk["code"]), hex(self.sprites[chunk["data"][3]][chunk["data"][2]]["flags"]))
                    sprite = self.sprites[chunk["data"][3]][chunk["data"][2]]["image"]
                    #TODO
                    # backgrounds are mirrored
                    # temple symbols are mirrored
                    # C11B mirrored
                    # char sprites are mirrored
                    if chunk["code"] & 0x0010:
                        sprite = PIL.ImageOps.flip(sprite)
                    if chunk["code"] & 0x0020:
                        sprite = PIL.ImageOps.mirror(sprite)
                    if chunk["code"] & 0x0080:
                        print("unknown flag 0x0080", hex(chunk["data"][-1]))
                    if len(chunk["data"]) > 4:
                        sprite = sprite.resize( (chunk["data"][4], chunk["data"][5]), resample=PIL.Image.NEAREST )
                    self.render_queue.append( (sprite, chunk["data"][0], chunk["data"][1]) )
                else:
                    print("sprite not loaded")
                pass
            elif chunk["code"] == 0xb600: # DRAW_SCREEN
                print("draw screen", chunk["data"][4:])
                self.render_queue.append( (self.screen, chunk["data"][0], chunk["data"][1]) )
                pass
            elif chunk["code"] == 0xc020: # LOAD_SOUNDRESOURCE
                # TODO sound
                pass
            elif chunk["code"] == 0xc030: # SELECT_SOUND
                pass
            elif chunk["code"] == 0xc040: # DESELECT_SOUND
                pass
            elif chunk["code"] == 0xc050: # PLAY_SOUND
                pass
            elif chunk["code"] == 0xc060: # STOP_SOUND
                pass
            elif chunk["code"] == 0xf010: # LOAD_SCREEN
                print("load screen", chunk["name"], chunk)
                self.screen = LoadSCX(resources[chunk["name"][:-1]+'X'])
                self.render_queue.append( (self.screen, 0, 0) )
                self.Render()
                self.Flip()
                pass
            elif chunk["code"] == 0xf020: # LOAD_IMAGE
                print("load sprite", chunk["name"])
                if chunk["name"][:-1]+'X' in resources:
                    self.sprites[self.sprite] = LoadBMX(resources[chunk["name"][:-1]+'X']) 
                pass
            elif chunk["code"] == 0xf050: # LOAD_PALETTE
                print("load palette")
                if chunk["name"] in resources:
                    self.palettes[self.palette] = LoadPAL(resources[chunk["name"]])["PAL"]
                pass
            else:
                print("unknown code", hex(chunk["code"]), chunk)

            self.index = self.index + 1
        else:
            self.tk.quit()
            pass

def BookScx():
    # TODO not done
    if False:
        print("===SCX===")
        key = "BOOK.SCX"
        SCX = resources[key]
        index = 1
        width = 640
        height = 350

        raw_size, = struct.unpack("<I", SCX[index:index+4])
        index = index + 4

        raw = Dynamix_LZW(raw_size, SCX[index:])
        raw = [j for i in raw for j in ((i & 0xF0) >> 4, (i & 0x0F))]

        library[key] = PIL.Image.frombytes("PA", (width, height), bytes([a for p in raw for a in (p, p if not p else 0xff)]).ljust(width * height, b'\x00'))

        palette = []
        for p in range(0xF):
            c = (0xFF // 0xF) * p
            palette.extend([c, c, c])
        palette += [0] * (768 - len(palette))

        library[key].putpalette(palette)

def ShowImage(image, palette):
    copy = image.copy()
    copy.putpalette(palette)
    copy.show()

def ShowMovieTk(movie):
    scale = 3

    tk = tkinter.Tk()
    tk.geometry("{}x{}+{}+{}".format(320*scale, 200*scale,(1920-320*scale)//2,(1080-200*scale)//2))
    tk.resizable(False, False)

    canvas = tkinter.Canvas(tk, width=320*scale, height=200*scale)
    canvas.pack(fill = tkinter.BOTH, expand = tkinter.YES)

    surface = PIL.ImageTk.PhotoImage(PIL.Image.new("RGB", (320*scale, 200*scale)))
    canvas.create_image(320*scale//2, 200*scale//2, image=surface)

    m = Movie(tk, surface, scale, movie, canvas)
    tk.after(1, m.Next)
    tk.bind("<space>", lambda e: m.Next())
    tk.bind("q", lambda e: tk.quit())

    tk.mainloop()

def ShowModelPlt(model):
    ax = plt.figure().add_subplot(111, projection="3d")
    span = 0
    for mesh in model["DAT"]["model"][0]["mesh"]:
        for edge in mesh["face"][0]["edge"]:
            x, y, z = list(zip(*edge["vertex"] + [ edge["vertex"][0] ]))
            span = max([ abs(p) for a in [x, y, z] for p in a ] + [ span ])
            ax.plot(x, y, z)
    ax.scatter( span, span, span )
    ax.scatter( -span, -span, 0 )
    plt.title(model["MAP"])
    plt.xlabel("X")
    plt.ylabel("Y")
    plt.show()

def VxV(A, B):
    return ( A[1]*B[2] - A[2]*B[1]
           , A[2]*B[0] - A[0]*B[2]
           , A[0]*B[1] - A[1]*B[0] )

def MxV(M, V):
    x = round(M[0]*V[0] + M[1]*V[1] + M[2]*V[2] + M[3]*V[3])
    y = round(M[4]*V[0] + M[5]*V[1] + M[6]*V[2] + M[7]*V[3])
    z = round(M[8]*V[0] + M[9]*V[1] + M[10]*V[2] + M[11]*V[3])
    w = round(M[12]*V[0] + M[13]*V[1] + M[14]*V[2] + M[15]*V[3])
    return (x, y, z, w)

def MxM(A, B):
    return ( A[0]*B[0]+A[1]*B[4]+A[2]*B[8]+A[3]*B[12], A[0]*B[1]+A[1]*B[5]+A[2]*B[9]+A[3]*B[13], A[0]*B[2]+A[1]*B[6]+A[2]*B[10]+A[3]*B[14], A[0]*B[3]+A[1]*B[7]+A[2]*B[11]+A[3]*B[15]
           , A[4]*B[0]+A[5]*B[4]+A[6]*B[8]+A[7]*B[12], A[4]*B[1]+A[5]*B[5]+A[6]*B[9]+A[7]*B[13], A[4]*B[2]+A[5]*B[6]+A[6]*B[10]+A[7]*B[14], A[4]*B[3]+A[5]*B[7]+A[6]*B[11]+A[7]*B[15]
           , A[8]*B[0]+A[9]*B[4]+A[10]*B[8]+A[11]*B[12], A[8]*B[1]+A[9]*B[5]+A[10]*B[9]+A[11]*B[13], A[8]*B[2]+A[9]*B[6]+A[10]*B[10]+A[11]*B[14], A[8]*B[3]+A[9]*B[7]+A[10]*B[11]+A[11]*B[15]
           , A[12]*B[0]+A[13]*B[4]+A[14]*B[8]+A[15]*B[12], A[12]*B[1]+A[13]*B[5]+A[14]*B[9]+A[15]*B[13], A[12]*B[2]+A[13]*B[6]+A[14]*B[10]+A[15]*B[14], A[12]*B[3]+A[13]*B[7]+A[14]*B[11]+A[15]*B[15] )

def T(V):
    return ( 1, 0, 0, V[0]
           , 0, 1, 0, V[1]
           , 0, 0, 1, V[2]
           , 0, 0, 0, 1 )

def S(V):
    return ( V[0], 0, 0, 0
           , 0, V[1], 0, 0
           , 0, 0, V[2], 0
           , 0, 0, 0, 1 )

def R(V):
    A       = math.cos(math.radians(V[0]))
    B       = math.sin(math.radians(V[0]))
    C       = math.cos(math.radians(V[1]))
    D       = math.sin(math.radians(V[1]))
    E       = math.cos(math.radians(V[2]))
    F       = math.sin(math.radians(V[2]))

    AD      =   A * D
    BD      =   B * D

    mat = [0]*16
    mat[0]  =   C * E
    mat[1]  =  -C * F
    mat[2]  =   D
    mat[4]  =  BD * E + A * F
    mat[5]  = -BD * F + A * E
    mat[6]  =  -B * C
    mat[8]  = -AD * E + B * F
    mat[9]  =  AD * F + B * E
    mat[10] =   A * C

    mat[3]  =  mat[7] = mat[11] = mat[12] = mat[13] = mat[14] = 0
    mat[15] =  1
    return mat

def perspective(fovy, aspect, zNear, zFar):
    rad = math.radians(fovy)
    tanHalfFovy = math.tan(rad / 2)

    Result = [0]*16
    Result[0*4+0] = 1 / (aspect * tanHalfFovy)
    Result[1*4+1] = 1 / (tanHalfFovy)
    Result[2*4+2] = - (zFar + zNear) / (zFar - zNear)
    Result[2*4+3] = - (2 * zFar * zNear) / (zFar - zNear)
    Result[3*4+2] = - 1
    return Result

def EdgeFunction(a, b, c):
    return (c[0] - a[0]) * (b[1] - a[1]) - (c[1] - a[1]) * (b[0] - a[0])

def raster(model_space, xpos, ypos, zpos, xrot, zrot):
    model_matrix = MxM(T( (xpos, ypos, zpos) ), R( (-xrot, 0, zrot) ))
    world_space = [ MxV(model_matrix, (*p, 1)) for p in model_space ]
    view_matrix = MxM(T( (0, 0, 0) ), R( (0, 0, 0) ))
    camera_space = [ MxV(view_matrix, p) for p in world_space ]
    projection_matrix = perspective(45, 320/200, 10, 50000)
    clip_space = [ MxV(projection_matrix, p) for p in camera_space ]
    ndc = [ (x/w, y/w, z/w, w/w) for (x, y, z, w) in clip_space if w != 0 and all(-b < p < b for p, b in zip((x, y, z), (w, w, w))) ]
    screen = [((1 + x) * 0.5 * 320, (1 - y) * 0.5 * 200, -z) for (x, y, _, w), (_, _, z, _) in zip( ndc, camera_space ) ]
    return screen

# Thanks to Scratchapixel for a crash-course in rendering
def render(surface, model_space, xpos, ypos, zpos, xrot, zrot):
    backbuffer = PIL.Image.new("RGBA", (320, 200), (0x40, 0x40, 0x40))

    depth = {}
    plane = {}
    for i, shape in enumerate( model_space ):
        V = shape["vertex"]

        # Normal vector to a Plane
        # 𝑣⃑₁=𝑟⃑₁−𝑟⃑₀=(𝑥₁−𝑥₀,𝑦₁−𝑦₀,𝑧₁−𝑧₀)
        # 𝑣⃑₂=𝑟⃑₂−𝑟⃑₀=(𝑥₂−𝑥₀,𝑦₂−𝑦₀,𝑧₂−𝑧₀)
        # 𝑛⃑=𝑣⃑₁×𝑣⃑₂
        𝑣1=[ 𝑟1n - 𝑟0n for 𝑟1n, 𝑟0n in zip( V[1], V[0] ) ]
        𝑣2=[ 𝑟2n - 𝑟0n for 𝑟2n, 𝑟0n in zip( V[2], V[0] ) ]
        𝑛 = VxV( 𝑣1, 𝑣2 )

        # Equation of the Plane
        # 𝑎(𝑥−𝑥₀)+𝑏(𝑦−𝑦₀)+𝑐(𝑧−𝑧₀)=0
        # 𝑎𝑥+𝑏𝑦+𝑐𝑧−(𝑎𝑥+𝑏𝑦+𝑐𝑧)
        # 𝑎𝑥+𝑏𝑦+𝑐𝑧+𝑑=0
        equation = ( 𝑛[0], 𝑛[1], 𝑛[2], -( 𝑛[0]*V[0][0] + 𝑛[1]*V[0][1] + 𝑛[2]*V[0][2] ) )
        reduce = math.gcd( *equation )
        equation = tuple( n / reduce for n in equation )

        # Group co-planar shapes together
        plane.setdefault(equation, []).append( i )
        V = raster(shape["vertex"], xpos, ypos, zpos, xrot, zrot)

        # Inverse Z
        V = [(Vn[0], Vn[1], 1/Vn[2]) for Vn in V]

        bbox = ( min([int(Vn[0]) for Vn in V])
               , min([int(Vn[1]) for Vn in V])
               , max([int(Vn[0]) for Vn in V])
               , max([int(Vn[1]) for Vn in V]) )

        if bbox[0] >= 320 or bbox[2] < 0 or bbox[1] >= 200 or bbox[3] < 0:
            continue

        for p in [(px, py) for px in range(bbox[0], bbox[2]) for py in range(bbox[1], bbox[3])]:
            edge = list( zip( V[1:]+V[0:1], V ) )
            λ = [ EdgeFunction(e[0], e[1], p) for e in edge ]
            if all(λn >= 0 for λn in λ):
                area = sum( λ )
                λ = [ λn / area for λn in λ ]
                z = 1 / sum( [ Vn[2] * λn for Vn, λn in zip( V, λ ) ] )

                # Track the depth per plane
                if z < depth.get( equation, float( 'inf' ) ):
                    depth[ equation ] = z

    # Sort planes by depth
    order = [ item[0] for item in sorted( depth.items(), key=lambda item: -item[1] ) ]

    # Painter's Algorithm
    # Draw each plane furthest to closest
    for equation in order:
        for i in plane[ equation ]:
            shape = model_space[i]
            V = raster(shape["vertex"], xpos, ypos, zpos, xrot, zrot)

            bbox = ( min([int(Vn[0]) for Vn in V])
                   , min([int(Vn[1]) for Vn in V])
                   , max([int(Vn[0]) for Vn in V])
                   , max([int(Vn[1]) for Vn in V]) )

            for p in [(px, py) for px in range(bbox[0], bbox[2]) for py in range(bbox[1], bbox[3])]:
                edge = list( zip( V[1:]+V[0:1], V ) )
                λ = [ EdgeFunction(e[0], e[1], p) for e in edge ]
                if all(λn >= 0 for λn in λ):
                    color_offset = shape["color1"] * 3
                    color = palette["PAL"]["VGA"][color_offset:color_offset+3]
                    backbuffer.putpixel( p, tuple( color ) )

    surface.paste(backbuffer.convert("RGB").resize((surface.width(), surface.height())))

def ShowModelTk(model):
    scale = 3

    tk = tkinter.Tk()

    viewFrame = tkinter.Frame( tk )
    viewFrame.pack( side=tkinter.LEFT )
    viewFrame.grid_columnconfigure( 0, minsize = 160 * scale )
    viewFrame.grid_rowconfigure( 0, minsize = 200 * scale )

    canvas = tkinter.Canvas( viewFrame )
    canvas['width'] = 320 * scale
    canvas['height'] = 200 * scale
    canvas.grid( row = 0, column = 0, sticky = 'nsew' )

    surface = PIL.ImageTk.PhotoImage(PIL.Image.new("RGB", ( int( canvas['width'] ), int( canvas['height'] ) )), master=canvas)
    canvas.create_image( int(-160 * scale) // 2, 0, anchor=tkinter.NW, image=surface )

    hrscroll = tkinter.Scrollbar( canvas )
    hrscroll['orient'] = tkinter.HORIZONTAL
    hrscroll.pack(side=tkinter.BOTTOM, fill=tkinter.X)
    hrscroll.set(0.0, 0.10)

    hpscroll = tkinter.Scrollbar( canvas )
    hpscroll['orient'] = tkinter.HORIZONTAL
    hpscroll.pack(side=tkinter.BOTTOM, fill=tkinter.X)
    hpscroll.set(0.45, 0.55)

    vrscroll = tkinter.Scrollbar( canvas )
    vrscroll['orient'] = tkinter.VERTICAL
    vrscroll.pack(side=tkinter.RIGHT, fill=tkinter.Y)
    vrscroll.set(0.20, 0.30)

    zpscroll = tkinter.Scrollbar( canvas )
    zpscroll['orient'] = tkinter.VERTICAL
    zpscroll.pack(side=tkinter.RIGHT, fill=tkinter.Y)
    zpscroll.set(0.9, 1.0)

    vpscroll = tkinter.Scrollbar( canvas )
    vpscroll['orient'] = tkinter.VERTICAL
    vpscroll.pack(side=tkinter.RIGHT, fill=tkinter.Y)
    vpscroll.set(0.45, 0.55)

    model_space = []
    def setscroll(scroll, limit, degree):
        if limit >= 0:
            degree = max(0, min(limit, degree))
        else:
            degree = min(0, max(limit, degree))

        start = float(degree) / limit * 0.9 
        scroll.set(start, start + 0.1)

        zrot = hrscroll.get()[0] / 0.9 * 360
        xpos = hpscroll.get()[0] / 0.9 * 5000 - 2500
        xrot = vrscroll.get()[0] / 0.9 * 360
        zpos = zpscroll.get()[0] / 0.9 * -10000
        ypos = vpscroll.get()[0] / 0.9 * -5000 + 2500
        render(surface, model_space, xpos, ypos, zpos, xrot, zrot)

    def view(scroll, limit, event, value, unit=None):
        if event == "moveto":
            setscroll(scroll, limit, float(value) / 0.9 * limit)
        elif event == "scroll":
            if unit == "units":
                setscroll(scroll, limit, scroll.get()[0] / 0.9 * limit + int(value))
            elif unit == "wheel":
                direction = (1, -1)[value < 0]
                while value:
                    setscroll(scroll, limit, scroll.get()[0] / 0.9 * limit + int(direction) * 5)
                    tk.update_idletasks()
                    value -= direction
            elif unit == "pages":
                setscroll(scroll, limit, scroll.get()[0] / 0.9 * limit + int(value) * 10)

    hrscroll.config( command=lambda *args: view(hrscroll, 360, *args) )
    hpscroll.config( command=lambda *args: view(hpscroll, 5000, *args) )
    vrscroll.config( command=lambda *args: view(vrscroll, 360, *args) )
    zpscroll.config( command=lambda *args: view(zpscroll, -10000, *args) )
    vpscroll.config( command=lambda *args: view(vpscroll, -5000, *args) )

    ctrlFrame = tkinter.Frame( tk )
    ctrlFrame.pack(side=tkinter.LEFT, fill=tkinter.Y)

    toggle_var = {}
    def toggleFaces():
        nonlocal model_space

        model_space = []
        for i, mesh in enumerate( model["DAT"]["model"][0]["mesh"] ):
            for j, edge in enumerate( mesh["face"][0]["edge"] ):
                if toggle_var[ i ].get() and toggle_var[ ( i, j ) ].get():
                    model_space.append( edge )

        zrot = hrscroll.get()[0] / 0.9 * 360
        xpos = hpscroll.get()[0] / 0.9 * 5000 - 2500
        xrot = vrscroll.get()[0] / 0.9 * 360
        zpos = zpscroll.get()[0] / 0.9 * -10000
        ypos = vpscroll.get()[0] / 0.9 * -5000 + 2500
        render(surface, model_space, xpos, ypos, zpos, xrot, zrot)

    def onDouble( event ):
        column = tree.identify_column( event.x )
        if column == '#1':
            iid = tree.identify_row( event.y )
            tree.set( iid, column=column, value='YesNo'.replace( tree.set( iid, column=column ), '' ) )
            parent = tree.parent( iid )
            if parent == '':
                toggle_var[ iid ].set( not toggle_var[ iid ].get() )
            else:
                toggle_var[ ( parent, iid ) ].set( not toggle_var[ ( parent, iid ) ].get() )
            toggleFaces()

    tree = tkinter.ttk.Treeview( ctrlFrame )
    tree['columns'] = ('show','depth')
    width = tkinter.font.Font().measure('Yes')
    tree.column( 'show', width=width )
    tree.column( 'depth', width=width )
    tree.column( '#0', width=width*2 )
    tree.bind( '<Double-1>', onDouble )
    # prevent treeview from executing default binds
    tree.bind( '<Double-1>', lambda e: 'break', '+' )
    tree.pack( side=tkinter.LEFT, fill = tkinter.BOTH, expand = tkinter.YES )

    sb = tkinter.Scrollbar( ctrlFrame )
    sb['orient'] = tkinter.VERTICAL
    sb['command'] = tree.yview
    tree['yscrollcommand'] = sb.set
    sb.pack( side=tkinter.RIGHT, fill=tkinter.Y )

    for i, mesh in enumerate( model["DAT"]["model"][0]["mesh"] ):
        parent = tree.insert( '', 'end', text=str( i ), values='Yes' )
        toggle_var[ i ] = toggle_var[ parent ] = tkinter.BooleanVar( tree, value=True )
        for j, _ in enumerate( mesh['face'][0]["edge"] ):
            child = tree.insert( parent, 'end', text=str( j ), values='Yes' )
            toggle_var[ ( i, j ) ] = toggle_var[ ( parent, child ) ] = tkinter.BooleanVar( tree, value=True )

    logFrame = tkinter.Frame( tk )
    logFrame.pack(side=tkinter.LEFT, fill=tkinter.Y)
    t = tkinter.Text( logFrame, width=25 )
    t.pack()

    # init
#    for iid in range(0,15):
#        #tree.set( iid, column='#1', value='YesNo'.replace( tree.set( iid, column='#1' ), '' ) )
#        toggle_var[ iid ].set( not toggle_var[ iid ].get() )
#    for iid in [9,13]:
#        #tree.set( iid, column='#1', value='YesNo'.replace( tree.set( iid, column='#1' ), '' ) )
#        toggle_var[ iid ].set( not toggle_var[ iid ].get() )
    toggleFaces()

    def dump(mod):
        t.delete( '1.0', tkinter.END )

    tk.bind("q", lambda e: tk.quit())
    tk.mainloop()

def ShowWorldPlt(world_space, color, label, pos, rot):
    view_matrix = MxM(T(pos), R(rot))
    camera_space = [ MxV(view_matrix, p) for p in world_space ]

    projection_matrix = perspective(45, 320/200, 1000, 50000)

    near = projection_matrix[2*4+3] / (projection_matrix[2*4+2] - 1.0)
    far = projection_matrix[2*4+3] / (projection_matrix[2*4+2] + 1.0)

    nearBottom = near * (projection_matrix[2*4+1] - 1) / projection_matrix[1*4+1]
    nearTop = near * (projection_matrix[2*4+1] + 1) / projection_matrix[1*4+1]
    nearLeft = near * (projection_matrix[2*4+0] - 1) / projection_matrix[0*4+0]
    nearRight = near * (projection_matrix[2*4+0] + 1) / projection_matrix[0*4+0]

    farBottom = far * (projection_matrix[2*4+1] - 1) / projection_matrix[1*4+1]
    farTop = far * (projection_matrix[2*4+1] + 1) / projection_matrix[1*4+1]
    farLeft = far * (projection_matrix[2*4+0] - 1) / projection_matrix[0*4+0]
    farRight = far * (projection_matrix[2*4+0] + 1) / projection_matrix[0*4+0]

    label = label if label else [ None ] * len( color )
    x, y, z, c, l = list(zip(*[(x, y, z, c, l) for (x, y, z, w), c, l in zip(camera_space, color, label) if farLeft < x < farRight and farBottom < y < farTop and near < z < far]))

    ax = plt.figure().add_subplot(111, projection="3d")
    ax.scatter(x, y, z, zdir='y', c=c)
    for i, txt in enumerate( l ):
        ax.text( x[i], z[i], y[i], txt )

    fust = [ (nearLeft, nearTop, near)
           , (nearRight, nearTop, near)
           , (nearRight, nearBottom, near)
           , (nearLeft, nearBottom, near)
           , (nearLeft, nearTop, near) ]
    x, z, y = list(zip(*fust))
    plt.plot(x, y, z, c="#FF0000")

    fust = [ (farLeft, farTop, far)
           , (farRight, farTop, far)
           , (farRight, farBottom, far)
           , (farLeft, farBottom, far)
           , (farLeft, farTop, far) ]
    x, z, y = list(zip(*fust))
    plt.plot(x, y, z, c="#FF0000")

    fust = [ (nearLeft, nearTop, near)
           , (nearRight, nearTop, near)
           , (farRight, farTop, far)
           , (farLeft, farTop, far)
           , (nearLeft, nearTop, near) ]
    x, z, y = list(zip(*fust))
    plt.plot(x, y, z, c="#FF0000")

    fust = [ (nearLeft, nearBottom, near)
           , (nearRight, nearBottom, near)
           , (farRight, farBottom, far)
           , (farLeft, farBottom, far)
           , (nearLeft, nearBottom, near) ]
    x, z, y = list(zip(*fust))
    plt.plot(x, y, z, c="#FF0000")

    plt.gca().set_aspect('equal', adjustable='box')
    plt.show()

# Rotate left: 0b1001 --> 0b0011
rol = lambda val, r_bits, max_bits: \
    (val << r_bits%max_bits) & (2**max_bits-1) | \
    ((val & (2**max_bits-1)) >> (max_bits-(r_bits%max_bits)))

# Rotate right: 0b1001 --> 0b1100
ror = lambda val, r_bits, max_bits: \
    ((val & (2**max_bits-1)) >> r_bits%max_bits) | \
    (val << (max_bits-(r_bits%max_bits)) & (2**max_bits-1))

if __name__ == "__main__":
    offsets = []
    with open("krondor.rmf", "rb") as rmf:
        data = rmf.read(2 + 2 + 2)
        packed_count, hash_seed, hash_shift = struct.unpack("<HHH", data)
        for _ in range(packed_count):
            data = rmf.read(13 + 2)
            filename, count = struct.unpack("<13sH", data)
            for _ in range(count):
                data = rmf.read(8)
                hash, offset = struct.unpack("<II", data)
                offsets.append((hash, offset))

    # Only one file for now
    resources = {}
    with open(filename.rstrip(b'\x00'), "rb") as r:
        for hash, offset in (offsets):
            r.seek(offset)
            data = r.read(13 + 4)
            name, size = struct.unpack("<13sI", data)
            name = name.rstrip(b'\x00').decode()
            resources[name] = r.read(size)
            # calc = [ord(c) for c in name.upper()]
            # calc[0] += hash_seed
            # calc = functools.reduce(lambda a, b: rol(a, hash_shift, 32) + b, calc)
            # calc = rol(calc, hash_shift, 32)
            # print("{} {:08X} {:08X}".format(name, hash, calc))

    with open("startup.gam", 'rb') as gam:
        resources["startup.gam"] = gam.read()

    with open("frp.sx", 'rb') as snd:
        resources["frp.sx"] = snd.read()

    library = {}

    # WLD
    zone = "01"
    palette = LoadPAL(resources["Z"+zone+".PAL"])
    horizon = LoadBMX(resources["Z"+zone+"H.BMX"])
    texture = LoadSCX(resources["Z"+zone+"L.SCX"])
    sprites = []
    for n in range(0, 6):
        name = "Z{}SLOT{}.BMX".format(zone, n)
        if name in resources:
            sprites += LoadBMX(resources[name])

    tiles = []
    for y in range(9, 24):
        for x in range(9, 24):
            name = "T{}{:02}{:02}.WLD".format(zone, x, y)
            if name in resources:
                tiles += LoadWLD(resources[name])
    table = LoadTBL(resources["Z"+zone+".TBL"])
    #pprint.pprint( table )

    # DEBUG - Everything below here is temporary for debugging

    if True:
        # TODO z fighting on buildings
        model = next( ( t for t in table if "house" == t["MAP"] ) )
        #ShowModelPlt(model)
        ShowModelTk(model)

    def colorize( map ):
        if "fire" in map:
            return "#F0C0C0"
        elif "tree" in map:
            return "#aef359"
        elif "body" in map:
            return "#6A0DAD"
        elif "tstone" in map:
            return "#6A0DAD"
        elif "house" in map:
            return "#D2B48C"
        elif "fence" in map:
            return "#D2B48C"
        elif "field" in map:
            return "#D2B48C"
        elif "corn" in map:
            return "#ffff00"
        elif "ground" in map:
            return "#000000"
        elif "sign" in map:
            return "#CCCCCC"
        elif "land" in map:
            return "#CCCCCC"
        elif "dirt" in map:
            return "#FF0000"
        elif "inn" in map:
            return "#FF0000"
        elif "box" in map:
            return "#FF0000"
        elif "chest" in map:
            return "#FF0000"
        elif "smth" in map:
            return "#FF0000"
        else:
            return "#0000FF"

    if False:
        world = [ (t["xloc"], 0, t["yloc"], 1) for t in tiles ]
        c = []
        l = []
        for t in tiles:
            c.append( colorize( table[t["type"]]["MAP"] ) )
            l.append( str(table[t["type"]]["MAP"]) + str(t["xloc"]) + str(t["yloc"]) )
        ShowWorldPlt(world, c, l, (669600, -1000, 1064800), (0, 180, 0))

    if False:
        def get_model(model):
            model_space = []
            for mesh in model["DAT"]["model"][0]["mesh"]:
                for edge in mesh["face"][0]["edge"]:
                    # convert model from z up to y up
                    v = [ MxV(R( (-90, 0, 0) ), (*v, 1))[0:3] for v in edge["vertex"] ]
                    model_space.append( ( v, edge["color1"] ) )
            return model_space

        world_space = []
        c = []
        for t in tiles:
            if "vertices" in table[t["type"]]["DAT"]:
                model_space = get_model(table[t["type"]])
                model_matrix = MxM(T( (t["xloc"], t["zloc"], t["yloc"], 1) ), R( (t["xrot"], t["zrot"], t["yrot"]) ))
                model_matrix = MxM(model_matrix, S( (table[t["type"]]["DAT"]["scale"], table[t["type"]]["DAT"]["scale"], table[t["type"]]["DAT"]["scale"]) ))
                world_space.extend( [ MxV(model_matrix, (*p, 1)) for (poly, text) in model_space for p in poly ] )
            c.extend( [ colorize( table[t["type"]]["MAP"] ) ] * ( len( world_space ) - len( c ) ) )

        ShowWorldPlt(world_space, c, [], (669600, -1000, 1064800), (0, 180, 0))

