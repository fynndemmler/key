package org.key_project.jmlediting.ui.test.preferencepages;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import org.eclipse.jface.preference.ColorSelector;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swtbot.eclipse.finder.SWTWorkbenchBot;
import org.eclipse.swtbot.swt.finder.widgets.SWTBotButton;
import org.junit.AfterClass;
import org.junit.Before;
import org.junit.BeforeClass;
import org.junit.Test;
import org.key_project.jmlediting.ui.preferencepages.JMLColorPreferencePage;
import org.key_project.jmlediting.ui.test.UITestUtils;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper;
import org.key_project.jmlediting.ui.util.JMLUiPreferencesHelper.ColorProperty;

/**
 * Testingplan:
 * <ul>
 * <li>First test, whether the color shown in the ColorSelector is the color
 * from JMLSettings</li>
 * <li>Test setting a new JML Color and check the Method other use to get the
 * JMLColor</li>
 * <li>Test afterwards the RestoreDefault Button and check again</li>
 * <li>At last test whether a new opening of the Preferences still show the
 * right color.</li>
 * </ul>
 *
 * @author Thomas Glaser
 *
 */
public class JMLColorPreferencePageTest {
   static SWTWorkbenchBot bot = new SWTWorkbenchBot();

   private SWTBotButton commentColorButton;

   @BeforeClass
   public static void init() {
      UITestUtils.prepareWorkbench(bot);
   }

   @Before
   public void openGlobalJMLColorSettings() {
      UITestUtils.openGlobalSettings(bot);
      bot.sleep(100);
      this.navigateToJMLColorSettings();
      this.setCommentColorButton();
      bot.sleep(1000);
   }

   @AfterClass
   public static void resetColor() {
      JMLUiPreferencesHelper.resetToDefault(ColorProperty.COMMENT);
   }

   /**
    * needed for setting the Color.
    */
   private void setCommentColorButton() {
      this.commentColorButton = bot.buttonWithId(
            JMLColorPreferencePage.TEST_KEY,
            ColorProperty.COMMENT.getPropertyName());
   }

   private void navigateToJMLColorSettings() {
      bot.tree().getTreeItem("JML").select().expand().getNode("Colors")
            .select();
   }

   /*
    * hack needed, because native Dialogs can't be testet with SWTBot
    */
   private void setColor(final RGB commentColor) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            final Object oSelector = JMLColorPreferencePageTest.this.commentColorButton.widget
                  .getData();
            assertTrue(oSelector instanceof ColorSelector);
            final ColorSelector selector = (ColorSelector) oSelector;
            selector.setColorValue(commentColor);

         }
      });
      bot.sleep(500);
   }

   /*
    * hack needed, because native Dialogs can't be testet with SWTBot
    */
   private void checkColor(final RGB colorToCheck) {
      Display.getDefault().syncExec(new Runnable() {
         @Override
         public void run() {
            final Object oSelector = JMLColorPreferencePageTest.this.commentColorButton.widget
                  .getData();
            assertTrue(oSelector instanceof ColorSelector);
            final ColorSelector selector = (ColorSelector) oSelector;
            assertEquals("ColorSelector doesn't show the right color",
                  colorToCheck, selector.getColorValue());
         }
      });
      bot.sleep(500);
   }

   /*
    * execute Testingplan
    */
   @Test
   public void testColorSettings() {
      // first check whether the ColorSelector shows the right color at the
      // beginning.
      this.checkColor(JMLUiPreferencesHelper
            .getWorkspaceJMLColor(ColorProperty.COMMENT));

      RGB testColor = new RGB(255, 0, 0);
      this.setColor(testColor);
      bot.button("Apply").click();
      // Need to wait until the UI events has been processed
      bot.sleep(1000);
      assertEquals("Not the right JML-Color was set.", testColor,
            JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT));
      bot.button("Restore Defaults").click();
      bot.button("Apply").click();
      bot.sleep(1000);
      assertEquals("Restore Default JML Color did not work.",
            ColorProperty.COMMENT.getDefaultColor(),
            JMLUiPreferencesHelper.getWorkspaceJMLColor(ColorProperty.COMMENT));

      // final test
      testColor = new RGB(0, 255, 0);
      this.setColor(testColor);
      bot.button("OK").click();
      bot.sleep(100);
      this.openGlobalJMLColorSettings();
      this.checkColor(JMLUiPreferencesHelper
            .getWorkspaceJMLColor(ColorProperty.COMMENT));
      this.checkColor(testColor);

      bot.button("OK").click();
   }
}