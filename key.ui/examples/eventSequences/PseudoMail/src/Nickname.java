/*public class Nickname {
    public String name;
    public String[] addresses = new String[4];

    public Nickname(String name) {
        this.name = name;
    }

    public boolean addAddress(String address) {
        for (int i = 0; i < addresses.length; ++i) {
            if (this.addresses[i] == null) {
                this.addresses[i] = address;
                return true;
            }
        }
        return false;
    }

    public boolean removeAddress(String address) {
        for (int i = 0; i < addresses.length; ++i) {
            if (this.addresses[i].equals(address)) {
                this.addresses[i] = null;
                return true;
            }
        }
        return false;
    }
}*/