/*public class AddressBook {
    private Nickname[] nicknames = new Nickname[999];

    public boolean addNickname(String name) {
        int freeIndex = -1;
        for (int i = 0; i < nicknames.length; ++i) {
            if (nicknames[i].equals(nickname)) {
                return false;
            }
            freeIndex = i;
        }
        if (freeIndex == nicknames.length) {
            return false;
        }
        Nickname nickname = new Nickname(name);
        nicknames[freeIndex] = nickname;
        return true;
    }
}*/