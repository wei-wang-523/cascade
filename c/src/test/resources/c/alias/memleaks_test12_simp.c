typedef long unsigned int size_t;
void kfree(void*);

struct ldv_list_head {
  struct ldv_list_head *next, *prev;
};

struct ldv_dvb_frontend {
  void *tuner_priv;
};

struct ldv_m88ts2022_config {
  struct ldv_dvb_frontend *fe;
};

struct ldv_i2c_adapter {
};

struct ldv_i2c_client {
  struct ldv_device dev;
  struct ldv_i2c_adapter *adapter;
  void *addr;
};

struct ldv_m88ts2022_priv {
  struct ldv_m88ts2022_config cfg;
  struct ldv_i2c_client *client;
};

struct ldv_i2c_msg {
  void *addr;
  int flags;
  int len;
  char *buf;
};

struct ldv_list_head ldv_global_msg_list = { &(ldv_global_msg_list), &(ldv_global_msg_list) };

struct ldv_msg {
  void *data;
  struct ldv_list_head list;
};

struct ldv_device {
  void *platform_data;
  void *driver_data;
  struct ldv_device *parent;
};

int __VERIFIER_nondet_int(void);
void *__VERIFIER_nondet_pointer(void);

void *ldv_malloc(size_t size) {
  if(__VERIFIER_nondet_int()) {
    return malloc(size);
  } else {
    return 0;
  }
};

static inline void LDV_INIT_LIST_HEAD(struct ldv_list_head *list)
{
  list->next = list;
  list->prev = list;
}

static inline void __ldv_list_add(struct ldv_list_head *new,
				  struct ldv_list_head *prev,
				  struct ldv_list_head *next)
{
  next->prev = new;
  new->next = next;
  new->prev = prev;
  prev->next = new;
}

static inline void ldv_list_add(struct ldv_list_head *new, struct ldv_list_head *head)
{
  __ldv_list_add(new, head, head->next);
}

int ldv_msg_fill(struct ldv_msg *msg) {
  void *data;
  data = ldv_malloc(len);
  if(!data) return - -3;
  msg->data = data;
  return 0;
}

int master_xfer(struct ldv_i2c_adapter *adap, struct ldv_i2c_msg *i2c_msg, int num) {
  struct ldv_msg *msg = (struct ldv_msg*)ldv_malloc(sizeof(struct ldv_msg));
  msg->data=0;
  LDV_INIT_LIST_HEAD(&msg->list);
  
  ldv_msg_fill(msg);
  ldv_list_add(&msg->list, &ldv_global_msg_list);
  return 0;
}

void main(void) {
  struct ldv_i2c_client *client = ldv_malloc(sizeof(struct ldv_i2c_client));
  struct ldv_m88ts2022_priv *priv = (struct ldv_m88ts2022_priv*)ldv_malloc(sizeof(struct ldv_m88ts2022_priv));
  memcpy(&priv->cfg, client->dev.platform_data, sizeof(struct ldv_m88ts2022_config));
  return;
}
