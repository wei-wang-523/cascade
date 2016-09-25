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

struct ldv_i2c_client {
  struct ldv_device dev;
  void *addr;
};

struct ldv_m88ts2022_priv {
  struct ldv_m88ts2022_config cfg;
  struct ldv_i2c_client *client;
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

void *ldv_malloc(size_t size) {
  return malloc(size); 
};

int master_xfer(int len) {
  struct ldv_msg *msg = (struct ldv_msg*)ldv_malloc(sizeof(struct ldv_msg));

  msg->list.next = &msg->list;
  msg->list.prev = &msg->list;
  msg->data = ldv_malloc(len);
  
  ldv_global_msg_list.next->prev = &msg->list;
  msg->list.next = ldv_global_msg_list.next;
  msg->list.prev = &ldv_global_msg_list;
  ldv_global_msg_list.next = &msg->list;
  
  return 0;
}

void main(void) {
  struct ldv_i2c_client *client = (struct ldv_i2c_client *)ldv_malloc(sizeof(struct ldv_i2c_client));
  struct ldv_m88ts2022_priv *priv = (struct ldv_m88ts2022_priv*)ldv_malloc(sizeof(struct ldv_m88ts2022_priv));
  memcpy(&priv->cfg, client->dev.platform_data, sizeof(struct ldv_m88ts2022_config));
  return;
}
