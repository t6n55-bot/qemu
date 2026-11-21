/* K10D companion-CPU (CPUCOM) model — see k10d_cpucom.c for the protocol facts. */
#ifndef K10D_CPUCOM_H
#define K10D_CPUCOM_H
#include <stdio.h>
#include <stdint.h>

int     k10d_cpucom_enabled(void);           /* FRN_DSP_MODEL=0 disables */
void    k10d_cpucom_txn_start(FILE *log);    /* status write with bit 0x200 */
void    k10d_cpucom_tx(uint8_t v);           /* main CPU wrote a data byte */
uint8_t k10d_cpucom_rx(FILE *log);           /* main CPU reads the simultaneous byte */
void     k10d_cpucom_raise_vec(int v);        /* FRN_MSG_FILE "!<vec>": pend vector once */
uint64_t k10d_cpucom_take_vecs(void);
extern volatile uint32_t k10d_cpucom_hold106;      /* forced input bits on 0x50000106 */
void     k10d_cpucom_hold_lines(uint32_t set, uint32_t clr);
int     k10d_cpucom_attention(void);         /* 1 = raise vector 31 now (edge) */
int     k10d_cpucom_pending(void);           /* companion request line (message pending) */
void    k10d_cpucom_post_msg(char c, const uint8_t *payload, int n);  /* FRN_MSG_FILE */
void    k10d_cpucom_tick(void);              /* per instruction: timed messages (FRN_KEYS) */

#endif
