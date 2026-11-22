/*
Zero-dependency macOS USB-C host CLI for Tricorder Bare-Metal OS (`VID=0x1209`, `PID=0x4701`).
Speaks CRC-32-verified `Kernel.Wire` frames directly over Bulk-OUT (`0x01`) / Bulk-IN (`0x81`).

Build:
  clang -O2 -Wall -Wextra -framework IOKit -framework CoreFoundation tools/tricorder_usb.c -o build/tricorder-usb

Usage:
  build/tricorder-usb ping
  build/tricorder-usb status
  build/tricorder-usb keys
  build/tricorder-usb push-descriptor <file>
  build/tricorder-usb push-override <psbt-file>
  build/tricorder-usb push-approve <psbt-file>
  build/tricorder-usb poll
*/
#include <CoreFoundation/CoreFoundation.h>
#include <IOKit/IOCFPlugIn.h>
#include <IOKit/IOKitLib.h>
#include <IOKit/usb/IOUSBLib.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TRICORDER_VID 0x1209
#define TRICORDER_PID 0x4701

static uint32_t crc32_ieee(uint8_t const * data, size_t len) {
    uint32_t crc = 0xFFFFFFFFu;
    for (size_t i = 0; i < len; i++) {
        crc ^= data[i];
        for (int b = 0; b < 8; b++) {
            crc = (crc & 1u) ? ((crc >> 1) ^ 0xEDB88320u) : (crc >> 1);
        }
    }
    return ~crc;
}

static uint8_t * encode_wire(uint8_t op, uint8_t const * payload, size_t plen, size_t * out_len) {
    size_t total = 8 + plen + 4;
    uint8_t * buf = malloc(total);
    if (!buf) return NULL;
    buf[0] = 'T'; buf[1] = 'R'; buf[2] = 'I'; buf[3] = 'W';
    buf[4] = op;
    buf[5] = 0;
    buf[6] = (uint8_t)(plen & 0xff);
    buf[7] = (uint8_t)((plen >> 8) & 0xff);
    if (plen > 0) memcpy(buf + 8, payload, plen);
    uint32_t crc = crc32_ieee(buf, 8 + plen);
    buf[8 + plen + 0] = (uint8_t)(crc & 0xff);
    buf[8 + plen + 1] = (uint8_t)((crc >> 8) & 0xff);
    buf[8 + plen + 2] = (uint8_t)((crc >> 16) & 0xff);
    buf[8 + plen + 3] = (uint8_t)((crc >> 24) & 0xff);
    *out_len = total;
    return buf;
}

static uint8_t * read_file_all(char const * path, size_t * out_len) {
    FILE * f = fopen(path, "rb");
    if (!f) { perror(path); return NULL; }
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (sz < 0 || sz > 32768) { fclose(f); return NULL; }
    uint8_t * buf = malloc((size_t)sz + 1);
    if (!buf) { fclose(f); return NULL; }
    if (sz > 0 && fread(buf, 1, (size_t)sz, f) != (size_t)sz) {
        free(buf); fclose(f); return NULL;
    }
    fclose(f);
    *out_len = (size_t)sz;
    return buf;
}

static IOUSBInterfaceInterface182 ** open_tricorder_iface(IOUSBDeviceInterface *** out_dev, uint8_t * out_pipe, uint8_t * in_pipe) {
    CFMutableDictionaryRef match = IOServiceMatching(kIOUSBDeviceClassName);
    int32_t vid = TRICORDER_VID, pid = TRICORDER_PID;
    CFNumberRef vidNum = CFNumberCreate(kCFAllocatorDefault, kCFNumberSInt32Type, &vid);
    CFNumberRef pidNum = CFNumberCreate(kCFAllocatorDefault, kCFNumberSInt32Type, &pid);
    CFDictionarySetValue(match, CFSTR(kUSBVendorID), vidNum);
    CFDictionarySetValue(match, CFSTR(kUSBProductID), pidNum);
    CFRelease(vidNum);
    CFRelease(pidNum);

    io_iterator_t iter = 0;
    if (IOServiceGetMatchingServices(kIOMainPortDefault, match, &iter) != KERN_SUCCESS) return NULL;
    io_service_t devSvc = IOIteratorNext(iter);
    IOObjectRelease(iter);
    if (!devSvc) return NULL;

    IOCFPlugInInterface ** plugIn = NULL;
    SInt32 score = 0;
    if (IOCreatePlugInInterfaceForService(devSvc, kIOUSBDeviceUserClientTypeID, kIOCFPlugInInterfaceID, &plugIn, &score) != KERN_SUCCESS) {
        IOObjectRelease(devSvc);
        return NULL;
    }
    IOObjectRelease(devSvc);

    IOUSBDeviceInterface ** dev = NULL;
    (*plugIn)->QueryInterface(plugIn, CFUUIDGetUUIDBytes(kIOUSBDeviceInterfaceID), (LPVOID *)&dev);
    (*plugIn)->Release(plugIn);
    if (!dev) return NULL;

    if ((*dev)->USBDeviceOpen(dev) != KERN_SUCCESS) {
        (*dev)->Release(dev);
        return NULL;
    }
    UInt8 curCfg = 0;
    IOUSBConfigurationDescriptorPtr cfgDesc = NULL;
    if ((*dev)->GetConfiguration(dev, &curCfg) != KERN_SUCCESS || curCfg == 0) {
        if ((*dev)->GetConfigurationDescriptorPtr(dev, 0, &cfgDesc) == KERN_SUCCESS && cfgDesc) {
            (*dev)->SetConfiguration(dev, cfgDesc->bConfigurationValue);
        }
    }

    IOUSBFindInterfaceRequest req;
    req.bInterfaceClass = kIOUSBFindInterfaceDontCare;
    req.bInterfaceSubClass = kIOUSBFindInterfaceDontCare;
    req.bInterfaceProtocol = kIOUSBFindInterfaceDontCare;
    req.bAlternateSetting = kIOUSBFindInterfaceDontCare;

    io_iterator_t ifIter = 0;
    (*dev)->CreateInterfaceIterator(dev, &req, &ifIter);
    io_service_t ifSvc = IOIteratorNext(ifIter);
    IOObjectRelease(ifIter);
    if (!ifSvc) { (*dev)->USBDeviceClose(dev); (*dev)->Release(dev); return NULL; }

    IOCFPlugInInterface ** ifPlug = NULL;
    IOCreatePlugInInterfaceForService(ifSvc, kIOUSBInterfaceUserClientTypeID, kIOCFPlugInInterfaceID, &ifPlug, &score);
    IOObjectRelease(ifSvc);
    if (!ifPlug) { (*dev)->USBDeviceClose(dev); (*dev)->Release(dev); return NULL; }

    IOUSBInterfaceInterface182 ** iface = NULL;
    (*ifPlug)->QueryInterface(ifPlug, CFUUIDGetUUIDBytes(kIOUSBInterfaceInterfaceID182), (LPVOID *)&iface);
    (*ifPlug)->Release(ifPlug);
    if (!iface || (*iface)->USBInterfaceOpen(iface) != KERN_SUCCESS) {
        if (iface) (*iface)->Release(iface);
        (*dev)->USBDeviceClose(dev);
        (*dev)->Release(dev);
        return NULL;
    }

    UInt8 numEps = 0;
    (*iface)->GetNumEndpoints(iface, &numEps);
    *out_pipe = 0; *in_pipe = 0;
    for (UInt8 p = 1; p <= numEps; p++) {
        UInt8 dir = 0, num = 0, xfer = 0, interval = 0;
        UInt16 mps = 0;
        if ((*iface)->GetPipeProperties(iface, p, &dir, &num, &xfer, &mps, &interval) == KERN_SUCCESS) {
            if (xfer == kUSBBulk && dir == kUSBOut) *out_pipe = p;
            if (xfer == kUSBBulk && dir == kUSBIn)  *in_pipe = p;
        }
    }
    *out_dev = dev;
    return iface;
}

int main(int argc, char ** argv) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s <ping|status|keys|push-descriptor|push-override|push-approve|poll|key> [arg]\n"
                        "  (note: `key <prev|next|select|back>` is non-mainnet test-only; proved rejected on mainnet)\n",
                argv[0]);
        return 2;
    }
    uint8_t op = 0;
    uint8_t * payload = NULL;
    size_t plen = 0;

    if (strcmp(argv[1], "ping") == 0) op = 0x01;
    else if (strcmp(argv[1], "status") == 0) op = 0x02;
    else if (strcmp(argv[1], "keys") == 0) op = 0x03;
    else if (strcmp(argv[1], "poll") == 0) op = 0x07;
    else if (strcmp(argv[1], "key") == 0 && argc >= 3) {
        op = 0x10;
        payload = malloc(1);
        plen = 1;
        if (strcmp(argv[2], "prev") == 0) payload[0] = 0;
        else if (strcmp(argv[2], "next") == 0) payload[0] = 1;
        else if (strcmp(argv[2], "select") == 0) payload[0] = 2;
        else if (strcmp(argv[2], "back") == 0) payload[0] = 3;
        else { fprintf(stderr, "bad key: %s\n", argv[2]); free(payload); return 2; }
    } else if (strcmp(argv[1], "push-descriptor") == 0 && argc >= 3) {
        op = 0x04; payload = read_file_all(argv[2], &plen); if (!payload) return 2;
    } else if (strcmp(argv[1], "push-override") == 0 && argc >= 3) {
        op = 0x05; payload = read_file_all(argv[2], &plen); if (!payload) return 2;
    } else if (strcmp(argv[1], "push-approve") == 0 && argc >= 3) {
        op = 0x06; payload = read_file_all(argv[2], &plen); if (!payload) return 2;
    } else {
        fprintf(stderr, "unknown command: %s\n", argv[1]);
        return 2;
    }

    uint8_t out_pipe = 0, in_pipe = 0;
    IOUSBDeviceInterface ** dev = NULL;
    IOUSBInterfaceInterface182 ** iface = open_tricorder_iface(&dev, &out_pipe, &in_pipe);
    if (!iface || !out_pipe || !in_pipe) {
        fprintf(stderr, "tricorder-usb: Tricorder Bare-Metal Signer (1209:4701) not found on USB-C\n");
        free(payload);
        return 1;
    }

    size_t flen = 0;
    uint8_t * frame = encode_wire(op, payload, plen, &flen);
    free(payload);
    IOReturn kr = (*iface)->WritePipeTO(iface, out_pipe, frame, (UInt32)flen, 3000, 3000);
    free(frame);
    if (kr != kIOReturnSuccess) {
        fprintf(stderr, "tricorder-usb: WritePipeTO failed (0x%08x)\n", kr);
        (*iface)->USBInterfaceClose(iface); (*iface)->Release(iface);
        (*dev)->USBDeviceClose(dev); (*dev)->Release(dev);
        return 1;
    }

    uint8_t rx[4096];
    UInt32 rxLen = sizeof(rx);
    kr = (*iface)->ReadPipeTO(iface, in_pipe, rx, &rxLen, 3000, 3000);
    if (kr != kIOReturnSuccess || rxLen < 12) {
        fprintf(stderr, "tricorder-usb: ReadPipeTO failed (kr=0x%08x len=%u)\n", kr, (unsigned)rxLen);
        (*iface)->USBInterfaceClose(iface); (*iface)->Release(iface);
        (*dev)->USBDeviceClose(dev); (*dev)->Release(dev);
        return 1;
    }
    if (memcmp(rx, "TRIW", 4) != 0) {
        fprintf(stderr, "tricorder-usb: bad reply magic\n");
        (*iface)->USBInterfaceClose(iface); (*iface)->Release(iface);
        (*dev)->USBDeviceClose(dev); (*dev)->Release(dev);
        return 1;
    }
    uint8_t rop = rx[4];
    uint16_t rlen = (uint16_t)rx[6] | ((uint16_t)rx[7] << 8);
    if ((size_t)(8 + rlen + 4) > rxLen) {
        fprintf(stderr, "tricorder-usb: truncated reply (%u < %u)\n", (unsigned)rxLen, (unsigned)(12 + rlen));
        (*iface)->USBInterfaceClose(iface); (*iface)->Release(iface);
        (*dev)->USBDeviceClose(dev); (*dev)->Release(dev);
        return 1;
    }
    uint32_t gotCrc = (uint32_t)rx[8 + rlen] | ((uint32_t)rx[9 + rlen] << 8) |
                      ((uint32_t)rx[10 + rlen] << 16) | ((uint32_t)rx[11 + rlen] << 24);
    uint32_t expCrc = crc32_ieee(rx, 8 + rlen);
    if (gotCrc != expCrc) {
        fprintf(stderr, "tricorder-usb: CRC-32 mismatch\n");
        (*iface)->USBInterfaceClose(iface); (*iface)->Release(iface);
        (*dev)->USBDeviceClose(dev); (*dev)->Release(dev);
        return 1;
    }
    printf("%s: %.*s\n", (rop == 0x80) ? "OK" : "ERR", (int)rlen, (char *)(rx + 8));
    (*iface)->USBInterfaceClose(iface);
    (*iface)->Release(iface);
    (*dev)->USBDeviceClose(dev);
    (*dev)->Release(dev);
    return (rop == 0x80) ? 0 : 1;
}
