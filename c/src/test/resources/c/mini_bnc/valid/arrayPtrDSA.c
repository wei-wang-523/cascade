struct ldv_i2c_msg {
  int flags;
  int len;
};

int main() {
  struct ldv_i2c_msg msg[2] = {
    {
      .flags = 0,
      .len = 1,
    }, {
      .flags = 1,
      .len = 1,
    }
  };
  
  struct ldv_i2c_msg* msgs = msg;
  int ret = msgs[0].len;
  return ret;
}