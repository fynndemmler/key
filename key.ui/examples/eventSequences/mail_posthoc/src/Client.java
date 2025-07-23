public final class Client {
    public String[] inbox = new String[999];
    private int mailIndex = 0;
    private String lastMsg = "";

    /*@ normal_behavior
    @ requires mail != null;
    @ ensures mail.isEncrypted == false;
    @ assignable mail.isEncrypted;
    @ pure
    @*/
    public void decrypt(Mail mail) {
        mail.isEncrypted = false;
    }

    /*@ normal_behavior
    @ requires mail != null && mail.content != null && inbox[mailIndex] != null;
    @ ensures inbox[\old(mailIndex)] == mail.content && \old(mailIndex) + 1 == mailIndex;
    @ assignable inbox[mailIndex], mailIndex, lastMsg;
    @ pure
    @*/
    public void addToInbox(Mail mail) {
        //this.inbox[mailIndex] = mail.content;
        lastMsg = mail.content;
        mailIndex += 1;
    }

    /*@ normal_behavior
    @ requires receiver != null && mail != null ;
    @ ensures mail.sent == true;
    @ assignable mail.sent;
    @ pure
    @*/
    public void send(Client receiver, Mail mail) {
        // Some code to send the mail
        mail.sent = true;
    }

    public void forward(Client receiver, Mail mail) {
        decrypt(mail);
        addToInbox(mail);
        send(receiver, mail);
    }
}